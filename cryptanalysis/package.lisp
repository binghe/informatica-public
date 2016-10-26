(in-package :cryptanalysis-system)

(defpackage cryptanalysis
  (:use :cl :crypto)
  (:shadowing-import-from #:crypto #:null)
  (:import-from #:crypto
    ;; API functions & macros
    #:defcipher
    #:defconst
    #:define-block-encryptor
    #:define-block-decryptor
    #:mod32ash
    #:rol32
    #:store-words #:with-words
    #:schedule-key
    ;; other symbols
    #:8-byte-block-mixin
    #:16-byte-block-mixin
    #:cipher
    #:context
    #:plaintext
    #:plaintext-start
    #:ciphertext
    #:ciphertext-start
    #:simple-octet-vector)
  (:export))
