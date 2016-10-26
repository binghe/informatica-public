(in-package :cryptanalysis)

(defparameter *des-test-key*
  (integer-to-octets #x0123456789abcdef :n-bits 64))

(defparameter *des-test-message*
  (integer-to-octets #x4e6f772069732074 :n-bits 64))

(defparameter *des-confirm-ciphertext*
  (integer-to-octets #x3fa40e8a984d4815 :n-bits 64))

(defvar *des-test-ciphertext*)

(defparameter *test-des* (make-cipher 'des :mode 'ecb :key *des-test-key*))

(defun print-message (message &optional verbose)
  (format t "message: #b~64,'0B~%" (octets-to-integer message))
  (when verbose
    (format t "message: #x~16,'0X~%" (octets-to-integer message))))

(defun print-ciphertext (ciphertext &optional verbose)
  (format t " cipher: #b~64,'0B~%" (octets-to-integer ciphertext))
  (when verbose
    (format t " cipher: #x~16,'0X~%" (octets-to-integer ciphertext))))

(defun test-des () ; NIL is success, number is failure
  (let ((*des-test-ciphertext* (integer-to-octets 0 :n-bits 64)))
    (print-message *des-test-message*)
    (encrypt *test-des* *des-test-message* *des-test-ciphertext*)
    (print-ciphertext *des-test-ciphertext*)
    (mismatch *des-test-ciphertext* *des-confirm-ciphertext*)))
