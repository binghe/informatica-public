(in-package :cryptanalysis)

#|
> (des-round-p-inverse #b10000000000000000000000000000000)
#b0000 0000 0000 0001 0000000000000000
|#

(defun des-round-p-inverse (output) ; 32-to-32
  (loop with input = 0
	for output-index from 0 to 31 ; array-index
	as output-pos = (- 31 output-index) ; {31 ... 0}
	as input-index = (aref +des-round-p+ output-index) ; {1 ... 32}
	as input-pos = (- 32 input-index) ; {31 ... 0} in input bits
	do (setq input (logior input
			       ;; use `ash' to move the output bits to correct position in input
			       (mod32ash (ldb (byte 1 output-pos) output) input-pos)))
	finally (return input)))

(defparameter *zero-key*
  (integer-to-octets 0 :n-bits 64))

(defparameter *des4-cipher*
  (make-cipher 'crypto::des4 :mode 'ecb :key *des-test-key*)) ; old: *zero-key*

;;;; Differential Cryptanalysis of DES Reduced to Four Rounds

(defun generate-random-message (&optional (n-bits 64))
  (integer-to-octets (#-lispworks-64bit random
                      #+lispworks-64bit nr300:random
                       (expt 2 64))
                     :n-bits n-bits))

(defun make-other-message (message difference &optional (n-bits 64))
  (let* ((m (octets-to-integer message))
	 (d (octets-to-integer difference))
	 (c (logxor m d)))
    (integer-to-octets c :n-bits n-bits)))

(defparameter *test-difference* (integer-to-octets #x2000000000000000 :n-bits 64))

(defun encrypt-des4 (message)
  (let ((message-1 (integer-to-octets message)) ;; #b0110010011101100101011011110000000001100011111100001011000010111))
	(ciphertext-1 (integer-to-octets 0 :n-bits 64)))
    (encrypt *des4-cipher* message-1 ciphertext-1)
    (print-ciphertext ciphertext-1)))

(defun generate-pairs (number difference
			      &aux (d (octets-to-integer difference)) (*verbose* (= number 1)))
  (format t "Generating message-ciphertext pairs using difference:
   diff: #b~64,'0B
   diff: #x~16,'0X~%~%" d d)
  (loop for i from 1 to number
	as message-1 = (generate-random-message)
	as message-2 = (make-other-message message-1 difference)
	as ciphertext-1 = (integer-to-octets 0 :n-bits 64)
	as ciphertext-2 = (integer-to-octets 0 :n-bits 64)
	as encryption-process-1 = (make-array 4)
	as encryption-process-2 = (make-array 4)
	do
    (print-message message-1)
    (print-message message-2)
    (let ((*encryption-process* encryption-process-1))
      (when *verbose* (terpri))
      (encrypt *des4-cipher* message-1 ciphertext-1)
      (print-ciphertext ciphertext-1))
    (let ((*encryption-process* encryption-process-2))
      (when *verbose* (terpri))
      (encrypt *des4-cipher* message-2 ciphertext-2)
      (print-ciphertext ciphertext-2))
    (when *verbose*
      (terpri)
      (print-encryption-process-difference encryption-process-1 encryption-process-2))
    (terpri)
	collect (cons ciphertext-1 ciphertext-2)))
#|
> (check-one-ciphertext-pair (car *sample-pairs*) #b010111 +des-s8+ 0)
|#

;;; S8 <--> sbox = +des-s8+, pos = 0
(defun check-one-ciphertext-pair (ciphertext-pair sub-key sbox sbox-pos)
  (declare (type (unsigned-byte 6) sub-key))
  (let ((se-1 0) (se-2 0)  ; `S_e' is the expansion of S-box (before mixing the sub-key)
	c1-left c2-left T_l-prim)
    (declare (type (unsigned-byte 48) d1 d2))
    (destructuring-bind (ciphertext-1 . ciphertext-2)  ciphertext-pair
      (with-words ((c1.left c1.right) ciphertext-1 0)
	(setq se-1 (des-round-expansion c1.right)) ; 32-to-48
	(setq c1-left c1.left)) ; 32 bits
      (with-words ((c2.left c2.right) ciphertext-2 0)
	(setq se-2 (des-round-expansion c2.right)) ; 32-to-48
	(setq c2-left c2.left)) ; 32 bits
      (setq T_l-prim (logxor c1-left c2-left)) ; 32 bits
      (let* ((inverted-output (des-round-p-inverse T_l-prim))
	     (S_od-prim (4-bits inverted-output (* 4 sbox-pos)))
	     (se-1.sbox (6-bits se-1 (* 6 sbox-pos)))
	     (se-2.sbox (6-bits se-2 (* 6 sbox-pos)))
	     (si-1.sbox (logxor se-1.sbox sub-key)) ; mixed with sub-key
	     (si-2.sbox (logxor se-2.sbox sub-key))) ; mixed with sub-key
	(= (logxor (des-sbox sbox si-1.sbox)
		   (des-sbox sbox si-2.sbox))
	   S_od-prim)))))

#|
> (count-ciphertext-pairs *sample-pairs* +des-s8+ 0)
NIL

|#

(defun count-ciphertext-pairs (ciphertext-pairs sbox sbox-pos)
  (loop for sub-key from 0 to 63
	when (loop for pair in ciphertext-pairs
		   always (check-one-ciphertext-pair pair sub-key sbox sbox-pos))
	collect sub-key))

(defun find-keys (ciphertext-pairs)
  (let ((k8 (count-ciphertext-pairs ciphertext-pairs +des-s8+ 0))
	(k7 (count-ciphertext-pairs ciphertext-pairs +des-s7+ 1))
	(k6 (count-ciphertext-pairs ciphertext-pairs +des-s6+ 2))
	(k5 (count-ciphertext-pairs ciphertext-pairs +des-s5+ 3))
	(k4 (count-ciphertext-pairs ciphertext-pairs +des-s4+ 4))
	(k3 (count-ciphertext-pairs ciphertext-pairs +des-s3+ 5))
	(k2 (count-ciphertext-pairs ciphertext-pairs +des-s2+ 6)))
    (format t "subkey2: ~A ~%" k2)
    (format t "subkey3: ~A ~%" k3)
    (format t "subkey4: ~A ~%" k4)
    (format t "subkey5: ~A ~%" k5)
    (format t "subkey6: ~A ~%" k6)
    (format t "subkey7: ~A ~%" k7)
    (format t "subkey8: ~A ~%" k8)
    (if (or (> (list-length k2) 1)
	    (> (list-length k3) 1)
	    (> (list-length k4) 1)
	    (> (list-length k5) 1)
	    (> (list-length k6) 1)
	    (> (list-length k7) 1)
	    (> (list-length k8) 1))
	(format t "need more pairs!~%")
      (format t "succeed.~%"))))

#|
CRYPTANALYSIS 146 > (find-keys (generate-pairs 4 *test-difference*))
Generating message-ciphertext pairs using difference:
   diff: #b0010000000000000000000000000000000000000000000000000000000000000
   diff: #x2000000000000000

message: #b0110111000010101111101010100100100111011111001000001110111010111
message: #b0100111000010101111101010100100100111011111001000001110111010111
 cipher: #b0001110010110111100110010011110010010011011010110101011011110000
 cipher: #b0110011100011001101000011001111001010111011011100100111001000100

message: #b1001110110001111011011001111100101001010000001010011010101110001
message: #b1011110110001111011011001111100101001010000001010011010101110001
 cipher: #b0101100110001111111100111110011001101101010011000111000101001011
 cipher: #b1111001001010011001100100001001111101100011010000101000100001011

message: #b0010001010100100111111000000001010000101101100001011000011001111
message: #b0000001010100100111111000000001010000101101100001011000011001111
 cipher: #b1101110101111110111110100000000001111001110000011100111011111000
 cipher: #b0000101011011000111111110010111011101100111010101001011101011000

message: #b1101011010010101111000111011110010000000011011111010101001110100
message: #b1111011010010101111000111011110010000000011011111010101001110100
 cipher: #b1100101100010001111110100010010001011010100010111110011111101010
 cipher: #b1101011111110001101001010001000111110011100010011110011100001010

subkey2: (40) 
subkey3: (39) 
subkey4: (18) 
subkey5: (41) 
subkey6: (24) 
subkey7: (9) 
subkey8: (23) 
succeed.
NIL

|#
