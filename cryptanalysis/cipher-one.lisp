;;;; The Block Cipher Companion
;;;;
;;;; Chapter 6. Differential Cryptanalysis: The Idea
;;;;

(in-package :cryptanalysis)

;;; S-Box: 
;;;  x    | 0 1 2 3 4 5 6 7 8 9 a b c d e f
;;;  S[x] | 6 4 c 5 0 7 2 e 1 f 3 d 8 a 9 b

(defvar *cipher-s-box* ; x --> S[x]
  (make-array 16 :element-type '(unsigned-byte 4)
	      :initial-contents '(#x6 #x4 #xC #x5 #x0 #x7 #x2 #xE #x1 #xF #x3 #xD #x8 #xA #x9 #xB)))

(defun cipher-S (x)
  (declare (type (unsigned-byte 4) x))
  (the (unsigned-byte 4) (aref *cipher-s-box* x)))

(defvar *cipher-s-box-invert* ; x --> S^-1[x] or S[x] --> x
  (make-array 16 :element-type '(unsigned-byte 4)
	      :initial-contents '(#x4 #x8 #x6 #xa #x1 #x3 #x0 #x5 #xC #xE #xD #xF #x2 #xB #x7 #x9)))

(defun cipher-R (x)
  (declare (type (unsigned-byte 4) x))
  (the (unsigned-byte 4) (aref *cipher-s-box-invert* x)))

(deftype 4-bit-cipher-key () '(unsigned-byte 4))

;;; CipherOne:
;;;
;;;      k_0                         k_1
;;;       |           +---+           |
;;; m --> + --> u --> | S | --> v --> + --> c
;;;                   +---+
;;; k = k_0 || k_1

;;; API.
(defclass crypto::cipher-one (cipher 8-byte-block-mixin)
  ((key-0 :accessor key-0 :type 4-bit-cipher-key)
   (key-1 :accessor key-1 :type 4-bit-cipher-key)))

;;; API. key = key-0 || key-1
(defmethod schedule-key ((cipher crypto::cipher-one) key)
  (setf (key-0 cipher) (logand #b1111 (aref key 0)))
  (setf (key-1 cipher) (logand #b1111 (aref key 1)))
  cipher)

;;; API.
(define-block-encryptor cipher-one 8 ; use only low 4 bits of the block
  (let ((k-0 (key-0 context))
	(k-1 (key-1 context)))
    (cipher-one-encrypt plaintext plaintext-start ciphertext ciphertext-start k-0 k-1)))

(defun cipher-one-encrypt (plaintext plaintext-start ciphertext ciphertext-start k-0 k-1)
  (declare (type (unsigned-byte 4) k-0 k-1))
  (let* ((m (logand (aref plaintext plaintext-start) #b1111))
	 (c (logxor (cipher-s (logxor m k-0)) k-1))) ; c = S[m + k_0] + k_1
    (declare (type (unsigned-byte 4) m c))
    (setf (aref ciphertext ciphertext-start) c)))

;;; API.
(define-block-decryptor cipher-one 8 ; use only low 4 bits of the block
  (let ((k-0 (key-0 context))
	(k-1 (key-1 context)))
    (cipher-one-decrypt ciphertext ciphertext-start plaintext plaintext-start k-0 k-1)))

(defun cipher-one-decrypt (ciphertext ciphertext-start plaintext plaintext-start k-0 k-1)
  (declare (type (unsigned-byte 4) k-0 k-1))
  (let* ((c (logand (aref ciphertext ciphertext-start) #b1111))
	 (m (logxor (cipher-R (logxor c k-1)) k-0))) ; m = S^-1[c + k_1] + k_0
    (declare (type (unsigned-byte 4) m c))
    (setf (aref plaintext plaintext-start) m)))

;;; API
(defcipher crypto::cipher-one
  (:encrypt-function cipher-one-encrypt-block)
  (:decrypt-function cipher-one-decrypt-block)
  (:block-length 8)
  (:key-length (:fixed 2)))


;;; Tests

(defparameter *cipher-one-test-key* ; #xD7
  (make-array 2 :element-type '(unsigned-byte 8) :initial-contents '(#xD #x7)))

(defvar *cipher-one-test-cipher*
  (make-cipher 'crypto::cipher-one :mode 'ecb :key *cipher-one-test-key*))

(defun encrypt-cipher-one (m)
  (declare (type (unsigned-byte 4) m))
  (let ((message (make-array 8 :element-type '(unsigned-byte 8) :initial-element 0))
	(ciphertext (make-array 8 :element-type '(unsigned-byte 8) :initial-element 0)))
    (setf (aref message 0) m)
    (encrypt *cipher-one-test-cipher* message ciphertext)
    (aref ciphertext 0)))

(defun decrypt-cipher-one (c)
  (declare (type (unsigned-byte 4) c))
  (let ((message (make-array 8 :element-type '(unsigned-byte 8) :initial-element 0))
	(ciphertext (make-array 8 :element-type '(unsigned-byte 8) :initial-element 0)))
    (setf (aref ciphertext 0) c)
    (decrypt *cipher-one-test-cipher* ciphertext message)
    (aref message 0)))


;;; Attack CipherOne using known texts

(defparameter *sample-message-ciphertext-pairs*
  '(((#xa . #x9) (#x5 . #x6))
    ((#x9 . #x7) (#x8 . #x0))))

(defun generate-random-pairs ()
  (let* ((m-1 (random 16))
	 (m-2 (random 16)))
    (if (= m-1 m-2) (setq m-2 (random 16)))
    (if (= m-1 m-2) (setq m-2 (random 16)))
    (if (= m-1 m-2) (setq m-2 (random 16)))
    (let ((c-1 (encrypt-cipher-one m-1))
	  (c-2 (encrypt-cipher-one m-2)))
      `((,m-1 . ,c-1) (,m-2 . ,c-2)))))

(defun generate-two-random-pairs ()
  (list (generate-random-pairs)
	(generate-random-pairs)))

(defun attack-cipher-one (list-of-message-ciphertext-pairs)
  (format t "Using random pairs: ~a~%" list-of-message-ciphertext-pairs)
  (loop with possible-k1 = nil
	for i from 1
	for message-ciphertext-pairs in list-of-message-ciphertext-pairs
	do
    (destructuring-bind ((m-1 . c-1) (m-2 . c-2)) message-ciphertext-pairs
      (let* ((diff-u (logxor m-1 m-2))
	     (k1? (loop for tt from 0 to #xf
			for uu = (logxor (cipher-r (logxor tt c-1)) (cipher-r (logxor tt c-2)))
			when (= uu diff-u) collect tt)))
	(format t "[round ~a] possible k_1: ~a~%" i k1?)
	(if (= i 1)
	    (setq possible-k1 k1?)
	  (setq possible-k1
		(nintersection possible-k1 k1?)))
	(when (cl:null possible-k1)
	  (format t "fail.")
	  (return-from attack-cipher-one))
	(when (= 1 (length possible-k1))
	  (format t "success: k_1 = ~a~%" (car possible-k1))
	  (return-from attack-cipher-one (car possible-k1)))))
    finally
      (format t "fail.~%")))

(defun attack-cipher-one-full (list-of-message-ciphertext-pairs)
  (let ((k-1 (attack-cipher-one list-of-message-ciphertext-pairs)))
    (when k-1
      (let* ((m (random 16))
	     (c (encrypt-cipher-one m))
	     (v (logxor c k-1))
	     (u (cipher-R v))
	     (k-0 (logxor m u)))
	(format t "success: k_0 = ~a~%" k-0)))))
