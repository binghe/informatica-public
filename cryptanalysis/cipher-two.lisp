(in-package :cryptanalysis)

;;; CipherTwo:
;;;
;;;      k_0                         k_1                         k_2
;;;       |           +---+           |           +---+           |
;;; m --> + --> u --> | S | --> v --> + --> w --> | S | --> x --> + --> c
;;;                   +---+                       +---+
;;;
;;; k = k_0 || k_1 || k_2

;;; API.
(defclass crypto::cipher-two (cipher 8-byte-block-mixin)
  ((key-0 :accessor key-0 :type 4-bit-cipher-key)
   (key-1 :accessor key-1 :type 4-bit-cipher-key)
   (key-2 :accessor key-2 :type 4-bit-cipher-key)))

;;; API. key = key-0 || key-1 || key-2
(defmethod schedule-key ((cipher crypto::cipher-two) key)
  (setf (key-0 cipher) (logand #b1111 (aref key 0)))
  (setf (key-1 cipher) (logand #b1111 (aref key 1)))
  (setf (key-2 cipher) (logand #b1111 (aref key 2)))
  cipher)

(defun cipher-two-encrypt (plaintext plaintext-start ciphertext ciphertext-start k-0 k-1 k-2)
  (declare (type (unsigned-byte 4) k-0 k-1 k-2))
  (let* ((m (logand (aref plaintext plaintext-start) #b1111))
	 (v (cipher-s (logxor m k-0))) ; v = S[m + k_0]
	 (x (cipher-s (logxor v k-1))) ; x = S[v + k_1]
	 (c (logxor x k-2))) ; c = x + k_2
    (declare (type (unsigned-byte 4) c))
    (setf (aref ciphertext ciphertext-start) c)))

;;; API.
(define-block-encryptor cipher-two 8 ; use only low 4 bits of the block
  (let ((k-0 (key-0 context))
	(k-1 (key-1 context))
	(k-2 (key-2 context)))
    (cipher-two-encrypt plaintext plaintext-start ciphertext ciphertext-start k-0 k-1 k-2)))

(defun cipher-two-decrypt (ciphertext ciphertext-start plaintext plaintext-start k-0 k-1 k-2)
  (declare (type (unsigned-byte 4) k-0 k-1 k-2))
  (let* ((c (logand (aref ciphertext ciphertext-start) #b1111))
	 (w (cipher-r (logxor c k-2))) ; w = S^-1[c + k_2]
	 (u (cipher-r (logxor w k-1))) ; u = S^-1[w + k_1]
	 (m (logxor u k-0))) ; m = u + k_0
    (declare (type (unsigned-byte 4) m))
    (setf (aref plaintext plaintext-start) m)))

;;; API.
(define-block-decryptor cipher-two 8 ; use only low 4 bits of the block
  (let ((k-0 (key-0 context))
	(k-1 (key-1 context))
	(k-2 (key-2 context)))
    (cipher-two-decrypt ciphertext ciphertext-start plaintext plaintext-start k-0 k-1 k-2)))

;;; API
(defcipher crypto::cipher-two
  (:encrypt-function cipher-two-encrypt-block)
  (:decrypt-function cipher-two-decrypt-block)
  (:block-length 8)
  (:key-length (:fixed 3)))

;;; Tests

(defparameter *cipher-two-test-key* ; #xD7
  (make-array 3 :element-type '(unsigned-byte 8)
	      :initial-contents '(#x1 #x2 #x3)))

(defvar *cipher-two-test-cipher*
  (make-cipher 'crypto::cipher-two :mode 'ecb :key *cipher-two-test-key*))

(defun encrypt-cipher-two (m)
  (declare (type (unsigned-byte 4) m))
  (let ((message (make-array 8 :element-type '(unsigned-byte 8) :initial-element 0))
	(ciphertext (make-array 8 :element-type '(unsigned-byte 8) :initial-element 0)))
    (setf (aref message 0) m)
    (encrypt *cipher-two-test-cipher* message ciphertext)
    (aref ciphertext 0)))

(defun decrypt-cipher-two (c)
  (declare (type (unsigned-byte 4) c))
  (let ((message (make-array 8 :element-type '(unsigned-byte 8) :initial-element 0))
	(ciphertext (make-array 8 :element-type '(unsigned-byte 8) :initial-element 0)))
    (setf (aref ciphertext 0) c)
    (decrypt *cipher-two-test-cipher* ciphertext message)
    (aref message 0)))


;;; TODO: Attack CipherTwo using chosen texts.

