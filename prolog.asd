(in-package :cl-user)
(defpackage prolog-asd
  (:use :cl :asdf))
(in-package :prolog-asd)

(defsystem prolog
  :version "0.1"
  :licence "MIT Licence"
  :encoding :utf-8
  :depends-on ()
  :components ((:file "package")
               (:file "auxfns" :depends-on ("package"))
               (:file "patmatch" :depends-on ("package" "auxfns"))
               (:file "unify" :depends-on ("package" "patmatch"))
               (:file "prolog" :depends-on ("package" "unify")))
  :description "Prolog on Common Lisp")
