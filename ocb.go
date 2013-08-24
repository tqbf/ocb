// Package ocb provides support for OCB mode encryption/decryption, 
// implementing Rogaway's OCB3 draft standard.
package ocb

// BUG(tqbf) Write an online version of this interface, like you'd
// use to encrypt a 1GB file, incrementally, with an io.Writer/Reader
// interface and a "Final"

import (
	"crypto/cipher"
	"encoding/binary"
	"bytes"
	"crypto/subtle"
	"errors"
)

func xor(a [2]uint64, b [2]uint64) [2]uint64 {
	a[0] ^= b[0]
	a[1] ^= b[1]
	return a
}

// double, an OCB primitve, is a bit-twiddly implementation of
// GF(2**128) multiplication
func double(block [2]uint64) [2]uint64 { 
// 	If S[1] == 0 then 
// 	  double(S) == (S[2..128] || 0);
// 	otherwise 
// 	  double(S) == (S[2..128] || 0) xor 
// 	      (zeros(120) || 10000111).

	if block[0] & 0x8000000000000000 == 0 {
		block[0] = (block[0] << 1) | (block[1] >> 63)
		block[1] = block[1] << 1
	} else {
		block[0] = (block[0] << 1) | (block[1] >> 63)
		block[1] = block[1] << 1
		b := [2]uint64{ 0, 135 }
		block = xor(block, b)				
	}

	return block
}

// encipher applies the block cipher's encrypt operation, which
// is simple, but in terms of uint64s instead of a 128 bit string
func (b *ocbtab) encipher(p [2]uint64) (ret [2]uint64) {
	var inp, out [16]byte
	binary.BigEndian.PutUint64(inp[0:], p[0])
	binary.BigEndian.PutUint64(inp[8:], p[1])
	b.b.Encrypt(out[0:], inp[0:])
	ret[0] = binary.BigEndian.Uint64(out[0:])
	ret[1] = binary.BigEndian.Uint64(out[8:])
	return
}

// decipher is the opposite of encipher
func (b *ocbtab) decipher(c [2]uint64) (ret [2]uint64) {
	var inp, out [16]byte
	binary.BigEndian.PutUint64(inp[0:], c[0])
	binary.BigEndian.PutUint64(inp[8:], c[1])
	b.b.Decrypt(out[0:], inp[0:])
	ret[0] = binary.BigEndian.Uint64(out[0:])
	ret[1] = binary.BigEndian.Uint64(out[8:])
	return
}

type ocbtab struct {
	max uint64
	star [2]uint64
	dollar [2]uint64
	ls [][2]uint64
	b cipher.Block
}

// An OcbCipher implements authenticated encryption with additional
// data (ie, data that is authenticated but not encrypted) using the
// OCB3 algorithm
type OcbCipher struct {
	b ocbtab
	Taglen uint
}

// New returns an OcbCipher object initialized from the 
// cipher/Block object (typicalLy: cipher/aes), with 
// the given authentication tag length, in bytes. Typical
// values for taglen are 12 and 16; don't make it low, as
// security is reduced with lower tag lengths.
func New(c cipher.Block, taglen uint) (ret OcbCipher) { 
	ret.b = buildTab(0, c)
	ret.Taglen = taglen
	return
}

// builds the initial state used for encryption, decryption, and
// additional data hashing.
func buildTab(bytes uint64, c cipher.Block) (ret ocbtab) {
	ret.b = c
	ret.max = (bytes / 16) + 1
	ret.star = ret.encipher([2]uint64{ 0, 0 })
	ret.dollar = double(ret.star)

	ret.ls = append(ret.ls, double(ret.dollar))

	// "max" is a hint here; we also generate and cache
	// these values lazily.
	for i := uint64(1); i <= ret.max; i++ { 
		ret.ls = append(ret.ls, double(ret.ls[i-1]))
	}

	return
}

// lazily generate the L_n value for the block numbered j
func (b *ocbtab) lvalue(j uint64) [2]uint64 {
	if j > b.max {
		for i := (b.max + 1); i <= j; i++ { 
			b.ls = append(b.ls, double(b.ls[i-1]))
		}

		b.max = j
	}

	return b.ls[j]
}

// count trailing zeroes in x; for each block in the message, 
// ntz(blocknumber) selects an L_n value for the "offset"
func ntz(x uint64) uint64 {
	var y uint64

	if x == 0 { return 64 }	

	n := uint64(63)
	y  = x << 32
	if y != 0 { n = n - 32 ; x = y }
	y  = x << 16
	if y != 0 { n = n - 16 ; x = y }
	y  = x << 8
	if y != 0 { n = n - 8 ; x = y }
	y  = x << 4
	if y != 0 { n = n - 4 ; x = y }
	y  = x << 2
	if y != 0 { n = n - 2 ; x = y }
	y  = x << 1
	if y != 0 { n = n - 1 ;  }

	return n
}

// hash applies the OCB3 HASH function to the "additional data" 
// of the message (the data that will be authenticated but not 
// included in the ciphertext).
func (b *ocbtab) hash(a []byte) [2]uint64 {
	var sum, off [2]uint64

	var i uint64 = 1

	if len(a) >= 16 {
		max := uint64(len(a) / 16)

		// the hash is closely related to the block transform
		for i = uint64(1); i <= max; i++ { 

                        //   M1              M2
                        //   |      	     | 	       
		        //   +-offset1       +-offset2 
		        //   |      	     | 	       
                        //  AES  	    AES
                        //   |		     | 	
		        //   +-offset1       +-offset2 
                        //   |		     | 
                        //   C1		     C2

			blk := [2]uint64{ 
				binary.BigEndian.Uint64(a[((i-1)*16):]),
				binary.BigEndian.Uint64(a[((i-1)*16)+8:]),
			}
	
			off = xor(off, b.lvalue(ntz(i)))
			sum = xor(sum, b.encipher(xor(blk, off)))
		}
	}

	spill := len(a) & 15
	if spill > 0 { 
		// ... but is different from the block xfrm 
		// in how it handles trailing bytes
		off = xor(off, b.star)

		// zero-pad the trailing bytes with a leading bit
		var fake [16]byte
		copy(fake[0:], a[(i-1)*16:])
		fake[spill] = 0x80

		blk := [2]uint64{ 
			binary.BigEndian.Uint64(fake[0:]),
			binary.BigEndian.Uint64(fake[8:]),
		}

		blk = xor(blk, off)
		sum = xor(sum, b.encipher(blk))
	}

	return sum
}

// offstart computes the starting offset value from the 
// nonce; all the Ktop, bottom, and stretch stuff is used
// to initialize the offset value
func (b *ocbtab) offstart(nonce [2]uint64) [2]uint64 {
	// BUG(tqbf) OCB3 provides a variable-length nonce, but
	// here we hardcode 96 bits; a smaller nonce probably doesn't hurt
	// security, but because of the formatting OCB3 does, will
	// break compat.
	nonce[0] &= 0xffffffff
	nonce[0] |= 0x0100000000

	// the bottom 6 bits of the nonce select which bits from 
	// the rest of the nonce we'll use for our 128 bit starting
	// offset
	bottom := uint64(nonce[1] & 63)
	nonce[1] &= ^uint64(63)

	ktop := b.encipher(nonce)

	// distribute the bits of the nonce over 192 bits
	stretch := [3]uint64{
		ktop[0],
		ktop[1], 
		ktop[0] ^ ((ktop[0] << 8) | (ktop[1] >> 56)),
	}

	// select 128 contiguous bits from the 192 bit expanded
	// nonce based on the "bottom" value
	return [2]uint64{ 
		((stretch[0] << bottom) | (stretch[1] >> (64-bottom))),
		((stretch[1] << bottom) | (stretch[2] >> (64-bottom))),	
	}
}

// see Encrypt for the interface
func encrypt(p []byte, a []byte, nonce [2]uint64, b *ocbtab) ([]byte, [2]uint64) {
	out := new(bytes.Buffer)

	// each block of the ciphertext is encrypted independently,
	// like ECB mode, but the blocks are "offset" (before/after 
	// encryption) by xor'ing them into a running stream of offset values
	// that depends on the nonce --- think of the way CTR generates
	// a keystream.
	off := b.offstart(nonce)
	sum := [2]uint64{}

	var i uint64 = 1
	if len(p) >= 16 {
	 	max := uint64(len(p) / 16)
	 	for i = uint64(1); i <= max; i++ { 
			// this is doing the same thing the HASH
			// function did, but also saving the 
			// ciphertext output

	 		blk := [2]uint64{ 
	 			binary.BigEndian.Uint64(p[((i-1)*16):]),
	 			binary.BigEndian.Uint64(p[((i-1)*16)+8:]),
	 		}
	 
	 		off = xor(off, b.lvalue(ntz(i)))
	 		sum = xor(sum, blk)
	 
	 		cblk := xor(off, b.encipher(xor(blk, off)))
	 		binary.Write(out, binary.BigEndian, cblk[0])
	 		binary.Write(out, binary.BigEndian, cblk[1])
	 	}	
	}
	
	spill := uint64(len(p) & 15)
	if spill > 0 { 
		// trailing bytes in the encryption function
		// are handled by creating a short keystream 
		// and XOR'ing the 0-padded plaintxt to it.

		off = xor(off, b.star)
		pblk := b.encipher(off)
		var pad [16]byte
		binary.BigEndian.PutUint64(pad[0:], pblk[0])
		binary.BigEndian.PutUint64(pad[8:], pblk[1])

		fake := [16]byte{}
		copy(fake[0:], p[(i-1)*16:])
		fake[spill] = 0x80
		blk := [2]uint64{ 
			binary.BigEndian.Uint64(fake[0:]),
			binary.BigEndian.Uint64(fake[8:]),		
		}

		for j := uint64(0); j < spill; j++ {
			out.WriteByte(p[((i-1)*16)+j] ^ pad[j])
		}

		sum = xor(sum, blk)
	}

	// form the authentication tag; ~96-128 bits of this
	// value will typically get tacked the end of the 
	// message
	tag := xor(
		b.encipher(
			xor(xor(sum, off), b.dollar)),
		b.hash(a)) // incorporate the A.D.

	return out.Bytes(), tag
}

// Encrypt generates an OCB3 ciphertext and authentication tag
// (both byte strings) from additional data "a", plaintext "p",
// and a nonce, which should currently be 96 bits wide, big endian,
// so that nonce[0] leads with 32 zero bits. 
//
// The security of OCB3 depends on the nonce value never repeating,
// but it doesn't need to be unpredictable or secret; if you encrypt
// 2+ messages with the same OcbCipher, you should have a convention
// for generating successive fresh nonce values for each. A better
// higher-level interface would do this for you.
//
// Encrypt returns the ciphertext and authentication tag as separate
// values, but you'll typically just concatenate them to form a single
// authenticated ciphertext byte string.
//
// The "additional data" field "a" authenticates metadata or context
// that you don't want to include with the ciphertext. For instance, 
// the A.D. field could authenticate a protocol header that must 
// be cleartext for the protocol to work; authenticating A.D. with the
// ciphertext allows you to for instance defend against replay attacks
// (authenticate a timestamp or sequence number)
func (o *OcbCipher) Encrypt(a []byte, p []byte, nonce [2]uint64) (c, t []byte) {
	c, tb := encrypt(p, a, nonce, &(o.b))
	var tagstr [16]byte
	binary.BigEndian.PutUint64(tagstr[0:], tb[0])
	binary.BigEndian.PutUint64(tagstr[8:], tb[1])
	return c, tagstr[16-(o.Taglen):]
}

// see Decrypt for the interface
func decrypt(c []byte, a []byte, nonce [2]uint64, intag []byte, b *ocbtab) ([]byte, error) {
	out := new(bytes.Buffer)
	off := b.offstart(nonce)
	sum := [2]uint64{}

	var i uint64 = 1
	if len(c) >= 16 {
		max := uint64(len(c) / 16)
		for i = uint64(1); i <= max; i++ { 
			// extremely straightforward; does essentially
			// what encrypt does, but with the Decrypt
			// transform from the block cipher
			blk := [2]uint64{ 
				binary.BigEndian.Uint64(c[((i-1)*16):]),
				binary.BigEndian.Uint64(c[((i-1)*16)+8:]),
			}
	
			off = xor(off, b.lvalue(ntz(i)))
			pblk := xor(off, b.decipher(xor(blk, off)))	
			sum = xor(sum, pblk)
	
			binary.Write(out, binary.BigEndian, pblk[0])
			binary.Write(out, binary.BigEndian, pblk[1])
		}	
	}

	spill := uint64(len(c) & 15)
	if spill > 0 { 
		off = xor(off, b.star)
		cblk := b.encipher(off)
		var pad [16]byte
		binary.BigEndian.PutUint64(pad[0:], cblk[0])
		binary.BigEndian.PutUint64(pad[8:], cblk[1])
		fake := [16]byte{}

		for j := uint64(0); j < spill; j++ {
			fake[j] = c[((i-1)*16)+j] ^ pad[j]
			out.WriteByte(fake[j])
		}
		
		fake[spill] = 0x80
		blk := [2]uint64{ 
			binary.BigEndian.Uint64(fake[0:]),
			binary.BigEndian.Uint64(fake[8:]),		
		}

		sum = xor(sum, blk)
	}

	tag := xor(
		b.encipher(
			xor(xor(sum, off), b.dollar)),
		b.hash(a))

	var tagstr [16]byte
	binary.BigEndian.PutUint64(tagstr[0:], tag[0])
	binary.BigEndian.PutUint64(tagstr[8:], tag[1])

	if subtle.ConstantTimeCompare(tagstr[16-len(intag):], intag) == 1 {
		return out.Bytes(), nil
	} 

	return nil, errors.New("invalid tag")
}

// Decrypt deciphers an OCB3 ciphertext; this code passes the OCB3 test
// vectors so might even decrypt data that this code didn't encrypt!
//
// Takes additional data "a", ciphertext "c", authentication tag "intag",
// and "nonce", handled the same way as described in Encrypt; the 
// sender and receiver of data would in some way agree on the value of
// the nonce.
//
// This function returns plaintext and no error if the authentication
// tag matches --- it won't if any bit of the ciphertext or tag is 
// altered --- and returns an empty string and an error if the 
// authentication tag fails. 
func (o *OcbCipher) Decrypt(a []byte, c []byte, intag []byte, nonce [2]uint64) (p []byte, err error) {
	p, err = decrypt(c, a, nonce, intag, &(o.b))
	return
}
