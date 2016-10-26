(in-package :cryptanalysis)

(defun do-initial-permutation (input input-start output output-start)
  (declare (type (simple-array (unsigned-byte 8) (*)) input output))
  (declare (type (integer 0 #.(- array-dimension-limit 8))
                 input-start output-start))
  ;; 64-bit block broken into two 32-bit parts: left right
  (with-words ((left right) input input-start)
    (let ((work 0)) ; just a temporary storage
      (declare (type (unsigned-byte 32) work))
      ;; (des-initial-permutation left right)
      (frob left right -4 #x0f0f0f0f)
      (frob left right -16 #x0000ffff)
      (frob right left -2 #x33333333)
      (frob right left -8 #x00ff00ff)
      (store-words output output-start left right))))

(defun do-final-permutation (input input-start output output-start)
  (declare (type (simple-array (unsigned-byte 8) (*)) input output))
  (declare (type (integer 0 #.(- array-dimension-limit 8))
                 input-start output-start))
  ;; 64-bit block broken into two 32-bit parts: left right
  (with-words ((right left) input input-start)
    (let ((work 0)) ; just a temporary storage
      (declare (type (unsigned-byte 32) work))
      (frob left right -8 #x00ff00ff)
      (frob left right -2 #x33333333)
      (frob right left -16 #x0000ffff)
      (frob right left -4 #x0f0f0f0f)
      (store-words output output-start right left))))

(defparameter *des4-test-message*
  (integer-to-octets #x4e6f772069732074 :n-bits 64))

(defparameter *des4-test-ciphertext*
  (integer-to-octets 0 :n-bits 64))

(defparameter *des4-confirm-ciphertext*
  (integer-to-octets #x3FA40E8A984D4815 :n-bits 64))

(defun test-initial-permutation (message)
  (let ((*des4-test-message* (integer-to-octets message :n-bits 64))
	(*des4-test-ciphertext* (integer-to-octets 0 :n-bits 64)))
    (print-message *des4-test-message*)
    (do-initial-permutation *des4-test-message* 0 *des4-test-ciphertext* 0)
    (print-ciphertext *des4-test-ciphertext*)))

(defun test-final-permutation (message)
  (let ((*des4-test-message* (integer-to-octets message :n-bits 64))
	(*des4-test-ciphertext* (integer-to-octets 0 :n-bits 64)))
    (print-message *des4-test-message*)
    (do-final-permutation *des4-test-message* 0 *des4-test-ciphertext* 0)
    (print-ciphertext *des4-test-ciphertext*)))

(defparameter *test-reduced-des*
  (make-cipher 'ironclad::reduced-des :mode 'ecb :key *des-test-key*))

(defun test-reduced-des ()
  (let ((*des4-test-message* (integer-to-octets 0 :n-bits 64))
	(*des4-test-ciphertext* (integer-to-octets 0 :n-bits 64)))
    (print-message *des4-test-message*)
    (encrypt *test-reduced-des* *des4-test-message* *des4-test-ciphertext*)
    (print-ciphertext *des4-test-ciphertext*)))

(defparameter *real-difference* (integer-to-octets #x0000000080000000 :n-bits 64))
