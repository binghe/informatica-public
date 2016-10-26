(in-package :asdf)

(defpackage #:cryptanalysis-system
  (:use :cl :asdf))

(in-package #:cryptanalysis-system)

(defun array-reader (stream subchar arg)
  (declare (ignore subchar))
  (let ((array-data (read stream nil stream nil))
        (array-element-type `(unsigned-byte ,arg)))
    ;; FIXME: need to make this work for multi-dimensional arrays
    `(make-array ,(length array-data) :element-type ',array-element-type
                :initial-contents ',array-data)))
    
(defparameter *ironclad-readtable*
  (let ((readtable (copy-readtable nil)))
    (set-dispatch-macro-character #\# #\@ #'array-reader readtable)
    readtable))

(defclass ironclad-source-file (asdf:cl-source-file) ())
(defclass txt-file (asdf:doc-file) ((type :initform "txt")))
(defclass css-file (asdf:doc-file) ((type :initform "css")))

(defsystem cryptanalysis
  :name "Cryptanalysis"
  :author "Chun Tian (binghe)"
  :version "0.1"
  :licence "MIT"
  :description "A cryptanalysis framework for Common Lisp"
  :default-component-class ironclad-source-file
  :depends-on (:ironclad)
  :components ((:file "package")
               (:file "cryptanalysis" :depends-on ("package"))
	       (:file "reduced-des" :depends-on ("package"))
	       (:file "test" :depends-on ("reduced-des"))
	       (:file "diff-reduced-des" :depends-on ("reduced-des" "test"))
	       (:file "cipher-one" :depends-on ("cryptanalysis"))
	       (:file "cipher-two" :depends-on ("cipher-one"))
	       (:file "des4" :depends-on ("reduced-des"))
	       (:file "des4-diff" :depends-on ("des4" "test"))
	       ))

(defun ironclad-implementation-features ()
  #+sbcl
  (list* sb-c:*backend-byte-order*
         (if (= sb-vm:n-word-bits 32)
             :32-bit
             :64-bit)
         :ironclad-fast-mod32-arithmetic
         :ironclad-gray-streams
         (when (member :x86-64 *features*)
           '(:ironclad-fast-mod64-arithmetic)))
  #+cmu
  (list (c:backend-byte-order c:*target-backend*)
        (if (= vm:word-bits 32)
            :32-bit
            :64-bit)
        :ironclad-fast-mod32-arithmetic
        :ironclad-gray-streams)
  #+allegro
  (list :ironclad-gray-streams)
  #+lispworks
  (list :ironclad-gray-streams
        ;; Disable due to problem reports from Lispworks users and
        ;; non-obviousness of the fix.
        #+nil
        (when (not (member :lispworks4 *features*))
          '(:ironclad-md5-lispworks-int32)))
  #+openmcl
  (list :ironclad-gray-streams)
  #-(or sbcl cmu allegro lispworks openmcl)
  nil)

(defmethod perform :around ((op asdf:compile-op) (c ironclad-source-file))
  (let ((*readtable* *ironclad-readtable*)
        (*print-base* 10)               ; INTERN'ing FORMAT'd symbols
        (*print-case* :upcase)
        #+sbcl (sb-ext:*inline-expansion-limit* (max sb-ext:*inline-expansion-limit* 1000))
        #+cmu (ext:*inline-expansion-limit* (max ext:*inline-expansion-limit* 1000))
        (*features* (append (ironclad-implementation-features) *features*)))
    (call-next-method)))
