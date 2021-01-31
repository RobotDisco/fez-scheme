;;; fez-scheme.el --- Trivial Scheme implemented in Elisp

;; Copyright (C) 2021 Gaelan D'costa

;; Author: Gaelan D'cost <gdcosta@gmail.com>
;; Version: 0.0.1
;; Keywords: scheme
;; URL: https://github.com/RobotDisco/fez-scheme

;;; Commentary:

;; This package contains my attempt to implement the exercises in
;; Christian Quinnec's textbook "Lisp in Small Pieces.", implemented
;; in the Emacs Lisp runtime.…

;;; Code:

;; Emacs Lisp and Scheme have different definitions for truth and falsity:
;; - Emacs Lisp declares that all values other than NIL are true.
;; - Scheme declares that all values other than #f are true.
;; Since we cannot depend on the defining language and the defined
;; language working the same way, we will have tp explicitly create
;; boolean values we can thus evaluate in a schemelike way.
(defvar fez-boolean-true '\#t)
(defvar fez-boolean-false '\#f)

;; a special token to represent (begin) since we can't take for
;; granted in Scheme that the empty list equates to NIL. [LISP pg. 10]
(defvar fez-empty-begin 'fez-empty-begin)

;; We need an empty environment to start with
(defvar fez-initial-env '())
;; We need a global environment for top-level things
(defvar fez-global-env fez-initial-env)

;; TODO we should use gensyms here since unlike scheme emacs lisp
;; macros are not hygenic
(defmacro definitial (name)
  "Create top level variable NAME with a trivial value of 'void to start."
  (progn (setq fez-global-env (cons (cons name 'void) fez-global-env))
	 'name))
(defmacro definitial1 (name value)
  "Create top level variable NAME with a value of VALUE to start."
  (progn (setq fez-global-env (cons (cons name value) fez-global-env))))

(defmacro defprimitive (name realfn arity)
  "Define a top level primitive procedure.

Use this to define foundational procedures that are implemented
purely in the backing Emacs Lisp runtime.  It will be invoked by
the symbol NAME,call the Emacs Lisp function REALFN, and we also
declare it to have the specified ARITY"
  (definitial1 name (lambda (vals)
		      (if (= arity (length vals))
			  (apply #'value vals) ;Do this in the backing runtime, not fez scheme
			(error "Called primitive `%s' with incorrect arity" name)))))


(defun fez-eval (expr env)
  "Evaluate Fez Scheme expression EXPR in environment ENV.
We aren't doing any arity-checking here outside of what the defining language (Emacs Lisp) itself does."
  (if (atom expr) ; an atom is anything that isn't a cons cell
      (cond ((symbolp expr)
	     ;; Are you a variable? Look up your value in our env. If you
	     ;; don't exist, just return yourself as is.
	     (fez-lookup expr env))
	    ((or (numberp expr) (stringp expr) (booleanp expr) (vectorp expr))
	     ;; You're a type of value that we're comfortable
	     ;; autoquoting i.e. evaluating you as the same as your
	     ;; representation.

	     ;; NOTE for future: emacs lisp characters are just
	     ;; integers used differently.
	     expr)
	    ;; You are strange, we cannot evaluate you.
	    (t (error "Cannot evaluate expression `%s'" expr))
	    )
    ;; Ok I guess you are a cons cell and we have to apply you like a function
    ;; (or function-like thing.)
    (let ((operator (car expr)))
      ;; There are a minimal number of special forms we implement
      ;; directly instead of using generic function application
      (cond ((eq operator 'quote) (cadr expr))
	    ;; Our scheme interpreter's if form has to jump some hoops
	    ;; because scheme's rules for booleans are different than
	    ;; how the boolean evaluations of the emacs lisp runtime
	    ;; are evaluated.
	    ((eq operator 'if) (if (not (eq (fez-eval (cadr expr) env)
					    fez-boolean-false))
				   (fez-eval (caddr expr) env)
				 (fez-eval (caadddr expr) env)))
	    ((eq operator 'begin) (fez-eprogn (cdr expr) env))
	    ((eq operator 'set!) (fez-update (cadr expr)
					     env
					     (fez-eval (caddr expr) env)))
	    ((eq operator 'lambda) (fez-make-function (cadr expr)
						      (cddr expr) env))
	    ;; Not a special form, so use generic function application!
	    (t (fez-apply (fez-eval (car expr) env)
			  (fez-eval-list (cdr expr) env)))))))

(defun fez-lookup (varname env)
  "Lookup value of VARNAME in environment ENV."
  (if (consp env)
      (if (eq (caar env) varname)
	  (cdar env)
	(fez-lookup varname (cdr env))) ; OPTIMIZE away more misplaced TCO
    (error "No such variable `%s' defined in environment" varname)))

(defun fez-eprogn (exprs env)
  "Serially execute sequence EXPRS of forms in environment ENV.
We just happen to return the value of the last form being evaluated."
  (if (consp exprs)
      (if (consp (cdr exprs))
	  (progn (fez-eval (car exprs) env)
		 ;; Lisp in Small Pieces assumes we can leverage tail
		 ;; call optimization here, but Emacs Lisp doesn't
		 ;; have TCO D:
		 ;; It'd be nice to do this in a way that doesn't use
		 ;; too much more of the backing Emacs Lisp runtime,
		 ;; future chapters of the book will likely cover
		 ;; this.
		 (fez-eprogn (cdr exprs) env)) ; OPTIMIZE
	;; Only one form was inside the begin form, so just evaluate it.
	(fez-eval (car exprs) env))
    ;; An edge case in case we evaluate (begin), return a special token since we can't take for granted in Scheme that the empty list equates to NIL.
    'fez-empty-begin))

(defun fez-eval-list (exprs env)
  "Take expression list EXPRS and return corresponding evaluations fromenvironment ENV."
  (if (consp exprs)
      (let ((first-expr (fez-eval (car exprs) env)))
	(cons first-expr
	      (fez-eval-list (cdr exprs) env)))
    '()))

(defun fez-update (varname env value)
  "Update variable VARNAME in environment ENV to have value VALUE."
  (if (consp env)
      ;; environment is not empty (i.e. is an alist with one+ item)
      (if (eq? (caar env) varname)
	  ;; Current head is an older variable, so update it
	  (progn (set-cdr! (car env) value)
		 value)
	;; Head is not our variable of interest, so move on
	;; OPTIMIZE we need to stop tail-calling here
	(fez-update varname (cdr env) value))
    ;; environment is an empty a-list
    (error "No such variable `%s' exists to update!" varname)))

(defun fez-extend (env varnames vals)
  "Extend environment ENV with varnames and values via VARNAMES AND VALS."
  (cond ((consp varnames) (if (consp vals)
			      (cons (cons (car varnames) (car vals))
				    (fez-extend env (cdr varnames) (cdr vals)))
			    (error "Too few values in list")))
	((null varnames) (if (null vals)
			     env
			   (error "Too many values in list")))
	;; We've covered mismatched lists and matched lists above so
	;; by this point we're down to single name/value to add. I
	;; guess scheme somehow allows for situations where a variable
	;; is assigned all remaining values and we do that by not
	;; using a nil-terminated sequence of cons cells?
	((symbolp varnames) (cons (cons varnames vals) env))))

(defun fez-apply (fn args)
  "Apply arguments in ARGS to the procedure FN."
  (if (functionp fn)
      (funcall fn args)
    (error "`%s' is not a function" fn)))

(defun fez-old-make-function (arglist body env)
  "Define function with arguments ARGLIST, performing BODY in environment ENV."
  (lambda (vals)
    (fez-eprogn body (fez-extend env arglist vals))))

;;; Since creatinv environments is currently annoying and difficult,
;;; let's create a few variables and foundational under-scheme functions
;;; from which our scheme programs can be built.
(definitial foo)
(definitial bar)
(definitial baz)
;; I guess fibonacci and factorials are good tests?
(definitial fib)
(definitial fact)

(defprimitive cons #'cons 2)
(defprimitive car #'car 1)
(defprimitive set-cdr! #'setcdr 2)
(defprimitive + #'+ 2)
(defprimitive eq? #'eq 2)
(defprimitive < #'< 2)

(provide 'fez-scheme)
;;; fez-scheme.el ends here
