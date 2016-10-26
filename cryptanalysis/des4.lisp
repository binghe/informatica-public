(in-package :cryptanalysis)

;;; the S-box consists of four rows labeled p_0 through p_3. Each row has 16 entries and the number
;;; 0 through 15 occur once, and only once. Therefore each row represents a permutation of the numbers
;;; {0,...,15}. The six-bit input is split into two parts. The outer two bits are used to choose a row
;;; of the S-box and the inner four bits are used to pick a column of the S-box. The entry identified
;;; in this way gives the four bits of output from the S-box.

(defparameter +des-s1+
  (make-array '(4 16) :element-type '(unsigned-byte 4)
	      :initial-contents
	      '((#xe 4 #xd 1 2 #xf #xb 8 3 #xa 6 #xc 5 9 0 7)    ; p0
		(0 #xf 7 4 #xe 2 #xd 1 #xa 6 #xc #xb 9 5 3 8)    ; p1
		(4 1 #xe 8 #xd 6 2 #xb #xf #xc 9 7 3 #xa 5 0)    ; p2
		(#xf #xc 8 2 4 9 1 7 5 #xb 3 #xe #xa 0 6 #xd)))) ; p3

(defparameter +des-s2+
  (make-array '(4 16) :element-type '(unsigned-byte 4)
	      :initial-contents
	      '((#xf 1 8 #xe 6 #xb 3 4 9 7 2 #xd #xc 0 5 #xa)
		(3 #xd 4 7 #xf 2 8 #xe #xc 0 1 #xa 6 9 #xb 5)
		(0 #xe 7 #xb #xa 4 #xd 1 5 8 #xc 6 9 3 2 #xf)
		(#xd 8 #xa 1 3 #xf 4 2 #xb 6 7 #xc 0 5 #xe 9))))

(defparameter +des-s3+
  (make-array '(4 16) :element-type '(unsigned-byte 4)
	      :initial-contents
	      '((#xa 0 9 #xe 6 3 #xf 5 1 #xd #xc 7 #xb 4 2 8)
		(#xd 7 0 9 3 4 6 #xa 2 8 5 #xe #xc #xb #xf 1)
		(#xd 6 4 9 8 #xf 3 0 #xb 1 2 #xc 5 #xa #xe 7)
		(1 #xa #xd 0 6 9 8 7 4 #xf #xe 3 #xb 5 2 #xc))))

(defparameter +des-s4+
  (make-array '(4 16) :element-type '(unsigned-byte 4)
	      :initial-contents
	      '((7 #xd #xe 3 0 6 9 #xa 1 2 8 5 #xb #xc 4 #xf)
		(#xd 8 #xb 5 6 #xf 0 3 4 7 2 #xc 1 #xa #xe 9)
		(#xa 6 9 0 #xc #xb 7 #xd #xf 1 3 #xe 5 2 8 4)
		(3 #xf 0 6 #xa 1 #xd 8 9 4 5 #xb #xc 7 2 #xe))))

(defparameter +des-s5+
  (make-array '(4 16) :element-type '(unsigned-byte 4)
	      :initial-contents
	      '((2 #xc 4 1 7 #xa #xb 6 8 5 3 #xf #xd 0 #xe 9)
		(#xe #xb 2 #xc 4 7 #xd 1 5 0 #xf #xa 3 9 8 6)
		(4 2 1 #xb #xa #xd 7 8 #xf 9 #xc 5 6 3 0 #xe)
		(#xb 8 #xc 7 1 #xe 2 #xd 6 #xf 0 9 #xa 4 5 3))))

(defparameter +des-s6+
  (make-array '(4 16) :element-type '(unsigned-byte 4)
	      :initial-contents
	      '((#xc 1 #xa #xf 9 2 6 8 0 #xd 3 4 #xe 7 5 #xb)
		(#xa #xf 4 2 7 #xc 9 5 6 1 #xd #xe 0 #xb 3 8)
		(9 #xe #xf 5 2 8 #xc 3 7 0 4 #xa 1 #xd #xb 6)
		(4 3 2 #xc 9 5 #xf #xa #xb #xe 1 7 6 0 8 #xd))))

(defparameter +des-s7+
  (make-array '(4 16) :element-type '(unsigned-byte 4)
	      :initial-contents
	      '((4 #xb 2 #xe #xf 0 8 #xd 3 #xc 9 7 5 #xa 6 1)
		(#xd 0 #xb 7 4 9 1 #xa #xe 3 5 #xc 2 #xf 8 6)
		(1 4 #xb #xd #xc 3 7 #xe #xa #xf 6 8 0 5 9 2)
		(6 #xb #xd 8 1 4 #xa 7 9 5 0 #xf #xe 2 3 #xc))))

(defparameter +des-s8+
  (make-array '(4 16) :element-type '(unsigned-byte 4)
	      :initial-contents
	      '((#xd 2 8 4 6 #xf #xb 1 #xa 9 3 #xe 5 0 #xc 7)
		(1 #xf #xd 8 #xa 3 7 4 #xc 5 6 #xb 0 #xe 9 2)
		(7 #xb 4 1 9 #xc #xe 2 0 6 #xa #xd #xf 3 5 8)
		(2 1 #xe 7 4 #xa 8 #xd #xf #xc 9 0 3 5 6 #xb))))

(defvar *des-sboxes*
  (make-array 8 :initial-contents (list +des-s1+ +des-s2+ +des-s3+ +des-s4+ +des-s5+ +des-s6+ +des-s7+ +des-s8+)))

(defun des-sbox (sbox input) ; 6-to-4
  (declare (type (simple-array (unsigned-byte 4) (4 16)) sbox)
	   (type (unsigned-byte 6) input))
  (let ((outer-bits (logior (ash (ldb (byte 1 5) input) 1)
			    (ldb (byte 1 0) input)))
	(inner-bits (ldb (byte 4 1) input)))
    (the (unsigned-byte 4)
	 (aref sbox outer-bits inner-bits))))

;;; The bitwise expansion E in DES. The tables should be intepreted as those
;;; for IP and IP^{-1} in that the first bit of the output of E is taken from the 32nd bit of the input.

;;; NOTE: when describing DES we will denote the leftmost bit position of the 64-bit block as bit 1,
;;; and label the bits as we move to the right, making the rightmost bit 64. This is th convention that
;;; was established in the original FIPS documentation and it is the one that we will use here.

;;; Today we would not label the bits {1 ... 64} but would most likely use {63 ... 0} to reflect modern
;;; software techniques. so, to convert, use this formula: <new> = 64 - <old>

(defparameter +des-round-e+
  (make-array 48
    :initial-contents '(32  1  2  3  4  5
			 4  5  6  7  8  9
			 8  9 10 11 12 13
			12 13 14 15 16 17
			16 17 18 19 20 21
			20 21 22 23 24 25
			24 25 26 27 28 29
			28 29 30 31 32 1)))

#|
> (des-round-expansion 1) ; only bit 32 is "1"
140737488355330 (= #b100000000000000000000000000000000000000000000010)

> (des-round-expansion #xffffffff)
281474976710655 (= #xffffffff)

> (des-round-expansion 0)
0
|#
(defun des-round-expansion (input) ; 32-to-48
  (declare (type (unsigned-byte 32) input))
  (loop with output = 0
	for output-index from 0 to 47 ; array index
	as output-pos = (- 47 output-index) ; {47 ... 0}
	as input-index = (aref +des-round-e+ output-index) ; {1...32}
	as input-pos = (- 32 input-index) ; {31 ... 0} in input bits
	do (setq output (logior output
				;; use `ash' to move the input bits to correct position in output
				(ash (ldb (byte 1 input-pos) input) output-pos)))
	finally (return (ldb (byte 48 0) output))))

;;; The bitwise permutation P in DES. The tables should be intepreted as those
;;; for IP and IP^{-1} in that the first bit of the output of P is taken from the 16th bit of the input.

(defparameter +des-round-p+
  (make-array 32
    :initial-contents '(16  7 20 21 29 12 28 17
			 1 15 23 26  5 18 31 10
			 2  8 24 14 32 27  3  9
			19 13 30  6 22 11  4 25)))

(defun des-round-p (input) ; 32-to-32
  (loop with output = 0
	for output-index from 0 to 31 ; array-index
	as output-pos = (- 31 output-index) ; {31 ... 0}
	as input-index = (aref +des-round-p+ output-index) ; {1 ... 32}
	as input-pos = (- 32 input-index) ; {31 ... 0} in input bits
	do (setq output (logior output
			       ;; use `ash' to move the output bits to correct position in input
			       (mod32ash (ldb (byte 1 input-pos) input) output-pos)))
	finally (return output)))

(defun des-sboxes (input) ; 48-to-32 bits
  (let ((s1.input (6-bits input 42)) ; 6 bits
	(s2.input (6-bits input 36)) ; 6 bits
	(s3.input (6-bits input 30)) ; 6 bits
	(s4.input (6-bits input 24)) ; 6 bits
	(s5.input (6-bits input 18)) ; 6 bits
	(s6.input (6-bits input 12)) ; 6 bits
	(s7.input (6-bits input 6))  ; 6 bits
	(s8.input (6-bits input 0))) ; 6 bits
    (let ((s1.output (des-sbox +des-s1+ s1.input))  ; 4 bits
	  (s2.output (des-sbox +des-s2+ s2.input))  ; 4 bits
	  (s3.output (des-sbox +des-s3+ s3.input))  ; 4 bits
	  (s4.output (des-sbox +des-s4+ s4.input))  ; 4 bits
	  (s5.output (des-sbox +des-s5+ s5.input))  ; 4 bits
	  (s6.output (des-sbox +des-s6+ s6.input))  ; 4 bits
	  (s7.output (des-sbox +des-s7+ s7.input))  ; 4 bits
	  (s8.output (des-sbox +des-s8+ s8.input))) ; 4 bits
      (let ((output ; 32 bits
	     (logior (ash s1.output 28)
		     (ash s2.output 24)
		     (ash s3.output 20)
		     (ash s4.output 16)
		     (ash s5.output 12)
		     (ash s6.output 8)
		     (ash s7.output 4)
		     s8.output)))
	output))))

(defvar *encryption-process*)
(defparameter *verbose* t)

(defun print-encryption-process-difference (encryption-process-1 encryption-process-2)
  (loop for index from 0 to 3
	as pbox-output-diff = (logxor (car (aref encryption-process-1 index))
				      (car (aref encryption-process-2 index)))
	as right-diff = (logxor (cdr (aref encryption-process-1 index))
				(cdr (aref encryption-process-2 index)))
	do
    (format t " |                                                |~%")
    (format t "(+)<--- ~8,'0X (~A) <--- F <--- ~8,'0X (~A) <---+ (round ~d)~%"
	    pbox-output-diff  (code-char (+ (char-code #\A) index))
	    right-diff        (code-char (+ (char-code #\a) index))
	    (1+ index))
    (format t " |                                                |~%")
    (terpri)))

(defmacro des4-round (left right keys index)
  `(let* ((subkey (aref ,keys ,index)) ; 48 bits
	  (expansion (des-round-expansion ,right)) ; 32-to-48 bits
	  (sbox-input (logxor subkey expansion))  ; 48 bits
	  (sbox-output (des-sboxes sbox-input)) ; 48-to-32 bits
	  (pbox-output (des-round-p sbox-output)) ; 32 bits
	  (new-left (logxor ,left pbox-output))) ; 32 bits
     (when (boundp '*encryption-process*)
       (setf (aref *encryption-process* ,index) (cons pbox-output ,right)))
     (when *verbose*
       (format t " +-<--- ~8,'0X                 ~8,'0X ---->---+~%" ,left ,right)
       (format t " |                                                |~%")
       (format t "(+)<--- ~8,'0X (~A) <--- F <--- ~8,'0X (~A) <---+ (round ~d)~%"
	       pbox-output  (code-char (+ (char-code #\A) ,index))
	       ,right       (code-char (+ (char-code #\a) ,index))
	       (1+ ,index))
       (format t " |                                                |~%")
       (format t " +----> ~8,'0X                 ~8,'0X ----<---+~%" new-left ,right)
       (terpri))
     (setq ,left new-left)))

(defun des4-munge-block (input input-start output output-start keys)
  (declare (type (simple-array (unsigned-byte 8) (*)) input output))
  (declare (type (integer 0 #.(- array-dimension-limit 8))
                 input-start output-start))
  (declare (type des4-round-keys keys))
  ;; 64-bit block broken into two 32-bit parts: left right
  (with-words ((left right) input input-start)
    (des4-round left right keys 0) ; round 1
    (des4-round right left keys 1) ; round 2
    (des4-round left right keys 2) ; round 3
    (des4-round right left keys 3) ; round 4
    (store-words output output-start right left)))

;;; ECB mode encryption and decryption

;; API
(defclass crypto::des4 (cipher 8-byte-block-mixin)
  ((encryption-keys :accessor encryption-keys :type des4-round-keys)
   (decryption-keys :accessor decryption-keys :type des4-round-keys)))

;; API
(define-block-encryptor des4 8
  (des4-munge-block plaintext plaintext-start ciphertext ciphertext-start
                   (encryption-keys context)))

;; API
(define-block-decryptor des4 8
  (des4-munge-block ciphertext ciphertext-start plaintext plaintext-start
                   (decryption-keys context)))



;;; The bit composition of the DES round keys k1,...,k16 in terms of their bit
;;; position in the user-supplied key k = l1 | l2 ... | l63 | l64

(defparameter +des-k1+
  (make-array 48 :initial-contents
    '(10 51 34 60 49 17 33 57  2  9 19 42
       3 35 26 25 44 58 59  1 36 27 18 41
      22 28 39 54 37  4 47 30  5 53 23 29 
      61 21 38 63 15 20 45 14 13 62 55 31)))

(defparameter +des-k2+
  (make-array 48 :initial-contents
    '( 2 43 26 52 41  9 25 49 59  1 11 34
      60 27 18 17 36 50 51 58 57 19 10 33
      14 20 31 46 29 63 39 22 28 45 15 21
      53 13 30 55  7 12 37  6  5 54 47 23)))

(defparameter +des-k3+
  (make-array 48 :initial-contents
    '(51 27 10 36 25 58  9 33 43 50 60 18
      44 11  2  1 49 34 35 42 41  3 59 17
      61  4 15 30 13 47 23  6 12 29 62  5 
      37 28 14 39 54 63 21 53 20 38 31  7)))

(defparameter +des-k4+
  (make-array 48 :initial-contents
    '(35 11 59 49  9 42 58 17 27 34 44  2
      57 60 51 50 33 18 19 26 25 52 43  1
      45 55 62 14 28 31  7 53 63 13 46 20
      21 12 61 23 38 47  5 37  4 22 15 54)))

(defparameter +des-subkeys+
  (make-array 4 :initial-contents (list +des-k1+ +des-k2+ +des-k3+ +des-k4+)))

#|
CRYPTANALYSIS 22 > (print-des-key *des-test-key*)
K = 00000 00100  10001 10100  01010 11001  11100 01001  10101 01111  00110 11110 1111 (64 bits)
NIL

CRYPTANALYSIS 23 > (print-des4-subkeys (compute-des4-encryption-keys *des-test-key*))
K1 = 000010110000001001100111100110110100100110100101
K2 = 011010011010011001011001001001010110101000100110
K3 = 010001011101010010001010101101000010100011010010
K4 = 011100101000100111010010101001011000001001010111
NIL
|#

(defvar *all-ones* (integer-to-octets (1- (expt 2 64)) :n-bits 64))

#|
CRYPTANALYSIS 24 > (print-des4-subkeys (compute-des4-encryption-keys *all-ones*))
K1 = 111111111111111111111111111111111111111111111111
K2 = 111111111111111111111111111111111111111111111111
K3 = 111111111111111111111111111111111111111111111111
K4 = 111111111111111111111111111111111111111111111111
NIL
|#

;;; key scheduling
(defun compute-des4-encryption-keys (key)
  (declare (type (simple-array (unsigned-byte 8) (8)) key))
  (let ((kn (make-array 4 :element-type '(unsigned-byte 48) :initial-element 0))
	(key-value (octets-to-integer key))) ; 64-bit
    ;; compute k1 ~ k4
    (loop for key-index from 0 to 3
	  do
      (loop with subkey = 0
	    for i from 0 to 47 ; 0-right-indexed position in the subkey
	    as pos = (aref (aref +des-subkeys+ key-index)
			   (1- (- 48 i))) ; 1-left-indexed position in the full key {1..64}
	    as key-bit = (ldb (byte 1 (- 64 pos)) key-value)
	    do
	(setq subkey (logior subkey (ash key-bit i)))
	    finally
	      (setf (aref kn key-index) subkey)))
    kn))

(defun print-des-key (key)
  (format t "K = ~64,'0B~%" (octets-to-integer key)))

(defun print-des4-subkeys (subkeys)
  (declare (type (simple-array (unsigned-byte 48) (4)) subkeys))
  (loop for i from 0 to 3
	as subkey = (aref subkeys i)
	do
    (format t "K~D = ~48,'0B~%" (1+ i) subkey)))

(deftype des4-round-keys () '(simple-array (unsigned-byte 48) (4)))

(defun des4-compute-round-keys (key)
  (let ((encryption-keys (compute-des4-encryption-keys key))
        (decryption-keys (make-array 4 :element-type '(unsigned-byte 48))))
    (declare (type des4-round-keys encryption-keys decryption-keys))
    (do ((i 0 (+ i 1)))
        ((= i 3)
         (values encryption-keys decryption-keys))
      (setf (aref decryption-keys i) (aref encryption-keys (- 3 (1+ i)))))))

;; API
(defmethod schedule-key ((cipher crypto::des4) key)
  (multiple-value-bind (encryption-keys decryption-keys)
      (des4-compute-round-keys key)
    (setf (encryption-keys cipher) encryption-keys
          (decryption-keys cipher) decryption-keys)
    cipher))

;; API
(defcipher crypto::des4
  (:encrypt-function des4-encrypt-block)
  (:decrypt-function des4-decrypt-block)
  (:block-length 8)
  (:key-length (:fixed 8)))
