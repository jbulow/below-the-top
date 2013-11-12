;;;; library for defining language semantics
;;;; Aaron Burrow : burrows.labs@gmail.com

;;;; components
;;;; > tokenizer, produces sexpressions from a string literal
;;;; > translation manager, translations against sexpressions

;;;; TODO
;;;; > How do we handle environments?
;;;;   + global and local environments; global environments must be shared
;;;;     between unconnected sexpressions
;;;; > How do we want to handle lists? Do we want to support eval_pair like
;;;    behavior in our infrastructure? Does it even make sense in our
;;;    model?

(proclaim '(optimize (debug 3)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;          Tokenizor
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun whitespace? (c)
  (member c '(#\Backspace #\Tab #\Newline #\Linefeed #\Page #\Space)))

(defun paren? (c)
  (member c '(#\( #\))))

(defun remove-trailing-paren (next-char-fn)
  (let ((c (funcall next-char-fn)))
    (cond ((null c) (error "no trailing paren!"))
          ((char= c #\)) nil)
          ((whitespace? c) (remove-trailing-paren next-char-fn))
          (t (error "remove-trailing-paren has unexpected character!")))))

(defun tokenize-parenlist (next-char-fn read-table)
  (let ((c (funcall next-char-fn))
        (exprs '()))
    (assert (char= c #\())
    (do ((char (funcall next-char-fn 'peek) (funcall next-char-fn 'peek)))
        ((char= char #\)) exprs)
      (let ((e (tokenize next-char-fn read-table)))
        (unless (zerop (length e))
          (push e exprs))))
    (remove-trailing-paren next-char-fn)
    (reverse exprs)))

;; caller must _know_ that the first character is 'valid'
(defun tokenize-characters (next-char-fn &optional (so-far ""))
  (let ((c (funcall next-char-fn)))
    (assert (not (string= c 'negative-space)))
    (cond ((null c) so-far)
          ((paren? c)
           (funcall next-char-fn 'unread)
           so-far)
          ((whitespace? c) so-far)
          (t (tokenize-characters next-char-fn (scat so-far c))))))

;;;; Tokenizes a single sexpr
;;;; > FIXME: we could treat #\( as a macro character
(defun tokenize (next-char-fn &optional read-table)
  (let ((c (funcall next-char-fn)))
    (cond ((null c) '())
          ((char= c #\()
           (funcall next-char-fn 'unread)
           (tokenize-parenlist next-char-fn read-table))
          ((whitespace? c) (tokenize next-char-fn read-table))
          ((read-macro? c read-table)
           (funcall (read-macro-fn c read-table) next-char-fn read-table))
          (t (funcall next-char-fn 'unread)
             (tokenize-characters next-char-fn)))))

(defun next-char-factory (expr)
  (let ((count 0))
    (lambda (&optional opt)
      (block factory
        (when (eq opt 'unread)
          (decf count)
          (return-from factory 'unread))
        (let ((do-inc (not (string= opt 'peek))))
          (unwind-protect
            (cond ((< count 0) 'negative-space)
                    ((>= count (length expr)) nil)
                    (t (elt expr count)))
            (when do-inc
              (incf count))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;       read macros
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun unquote-handler (next-char-fn read-table)
  (let ((next-char (funcall next-char-fn 'peek)))
    (cond ((char= #\@ next-char)
           (funcall next-char-fn)
           (list "unquote-splicing" (tokenize next-char-fn read-table)))
          (t (list "unquote" (tokenize next-char-fn read-table))))))

(defun read-macro? (c read-table)
  (assoc c read-table :test #'char=))

(defun read-macro-fn (c read-table)
  (assert (read-macro? c read-table))
  (cdr (assoc c read-table)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;    Transformation Manager
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; > each type of object must be able to handle each type of
;;;;   transformation

(defstruct transformer
  name)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; default fail transformer
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmethod inform ((object basic-object)
                   (transformer-name symbol)
                   (whatami symbol))
  (error "object of type ~A doesn't implement 'inform' on ~A"
         (type-of object) transformer-name))

(defmethod pass ((object basic-object)
                 (transformer-name symbol)
                 (args list))
  (error "object of type ~A doesn't implement 'pass' on ~A"
         (type-of object) transformer-name))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;    noop transformer
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmethod inform ((object basic-object)
                   (transformer-name (eql 'noop))
                   (whatami (eql 'arg)))
  (cons nil object))

(defmethod inform ((object basic-object)
                   (transformer-name (eql 'noop))
                   (whatami (eql 'lead)))
  t)

(defmethod pass ((object basic-object)
                 (transformer-name (eql 'noop))
                 (args list))
  (cons nil (append (list object) args)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;     infrastructure
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun back-talk-arg (transformer expr)
  (declare (special *ctx*))
  (assert (typep expr 'atom))
  ;; response : (transform-more? . sexpr)
  (let ((response (inform expr (transformer-name transformer) 'arg)))
    (if (car response)
        (transform transformer (cdr response) *ctx*)
        (cdr response))))

(defun back-talk-sexpr (transformer lead &key expr-args)
  (declare (special *ctx*))
  (assert (typep expr-args 'list))
  ;; response : can-i-talk-to-your-arguments?
  (let* ((response (inform lead (transformer-name transformer) 'lead))
         (args (mapcar #'(lambda (a)
                           (if response
                               (transform transformer a *ctx*)
                               (identity a)))
                       expr-args)))
      ;; response : (transform-more? . sexpr)
      (let ((response-2
              (pass lead (transformer-name transformer) args)))
        (if (car response-2)
            (transform transformer (cdr response-2) *ctx*)
            (cdr response-2)))))

;;; transform a single expression {sexpression, atom}
(defun transform (transformer expr ctx)
  (let ((*ctx* ctx))
    (declare (special *ctx*))
    (cond ((atom expr) (back-talk-arg transformer expr))
          ((null expr) '())
          (t
            (back-talk-sexpr transformer
                             (car expr)
                             :expr-args (cdr expr))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;            maru
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defclass maru-env ()
  ((bindings :accessor maru-env-bindings
             :initarg  :bindings
             :initform '())
   (parent :accessor maru-env-parent
           :initarg   :parent
           :initform  nil
           :type maru-env)))

(defstruct maru-context
  env
  symbols)

(defun maru-mk-ctx (&key parent)
  (let ((env (make-instance 'maru-env
                :bindings nil
                :parent parent)))
    (make-maru-context :env env :symbols nil)))

(defun maru-parent-ctx (ctx)
  (let ((new-ctx (copy-structure ctx)))
    (setf (maru-context-env new-ctx)
          (maru-env-parent (maru-context-env ctx)))
    new-ctx))

(defun maru-intern (ctx text)
  (let ((symbol (mk-symbol text)))
    (car (push symbol (maru-context-symbols ctx)))))

(defun maru-define (ctx symbol obj)
  (assert (typep symbol 'symbol-object))
  (when (maru-lookup ctx symbol)
    (warn-me "redefining symbol"))
  (car (push (cons symbol obj)
             (maru-env-bindings (maru-context-env ctx)))))

(defun maru-lookup (ctx symbol)
  (unless (member symbol (maru-context-symbols ctx) :test #'eq-object)
    (error (format nil "symbol ~A has not been interned!"
                       (object-value symbol))))
  (labels ((l-up (env)
             (when (null env)
               (return-from l-up nil))
             (let ((bins (maru-env-bindings env)))
               (cond ((assoc symbol bins :test #'eq-object)
                      (cdr (assoc symbol bins :test #'eq-object)))
                     (t (l-up (maru-env-parent env)))))))
    (l-up (maru-context-env ctx))))

;;; > intern primitives and add their bindings to global env
;;; > add runtime compositioners
;;;     + *expanders*   : []
;;;     + *evaluators*  : [eval-symbol]
;;;     + *applicators* : [apply-fixed, apply-expr]
(defun maru-initialize ()
  (let ((ctx (maru-mk-ctx)))
    ;; primitives
    (maru-define ctx (maru-intern ctx "if")
                     (mk-fixed #'maru-primitive-if))
    (maru-intern ctx "t")
    (maru-define ctx (maru-intern ctx "cons")
                     (mk-expr #'maru-primitive-cons))
    (maru-define ctx (maru-intern ctx "car")
                     (mk-expr #'maru-primitive-car))
    (maru-define ctx (maru-intern ctx "cdr")
                     (mk-expr #'maru-primitive-cdr))

    ;; compositioners
    (maru-define ctx (maru-intern ctx "*expanders*") (mk-array 32))
    (maru-define ctx (maru-intern ctx "*evaluators*") (mk-array 32))
    (maru-define ctx (maru-intern ctx "*applicators*") (mk-array 32))

    ctx))

(defun maru-eval (ctx expr)
  (declare (ignore ctx expr))
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;      maru primitives
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; fixed
(defun maru-primitive-if (ctx &rest args)
  (let ((test (car args))
        (then (cadr args))
        (else (cddr args))
        (eval-transformer (make-transformer :name 'eval)))
    (if (not (maru-nil? (transform eval-transformer test ctx)))
        (transform eval-transformer then ctx)
        (let ((out nil))
          (dolist (e else out)                    ; implicit block
            (setf out (transform eval-transformer e ctx)))))))

; expr
(defun maru-primitive-cons (ctx &rest args)
  (declare (ignore ctx))
  (assert (= 2 (length args)))
  (cons (car args) (cadr args)))

; expr
(defun maru-primitive-car (ctx &rest args)
  (declare (ignore ctx args))
  nil)

; expr
(defun maru-primitive-cdr (ctx &rest args)
  (declare (ignore ctx args))
  nil)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;  maru type transformer
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defclass basic-object ()
  ())

(defclass single-value-object (basic-object)
  ((value :accessor object-value
          :initarg  :value)))

(defclass untyped-object (single-value-object)
  ())

(defun mk-untyped (value)
  (make-instance 'untyped-object :value value))

(defclass symbol-object (single-value-object)
  ())

(defun mk-symbol (value)
  (make-instance 'symbol-object :value value))

(defclass list-object (basic-object)
  ((elements :accessor list-object-elements
             :initarg  :elements)))

;;; unclear whether we should use 'mk-pair' instead
;;; > using a list object is nice because we easily represent nil with
;;;   the empty list
(defun mk-list (&rest elements)
  (make-instance 'list-object :elements elements))

(defclass number-object (single-value-object)
  ())

(defun mk-number (value &key hex)
  (make-instance 'number-object
                 :value (read-from-string (if hex
                                              (scat "#x" value)
                                              value))))

(defclass string-object (single-value-object)
  ())

(defun mk-string (value)
  (make-instance 'string-object :value value))

(defclass char-object (single-value-object)
  ())

(defun mk-char (value)
  (make-instance 'char-object :value value))

(defclass array-object (basic-object)
  ((elements :accessor array-object-elements
             :initarg  :elements)))

(defun mk-array (size)
  (make-instance 'array-object :elements (make-array size)))

(defclass function-object (basic-object)
  ((function :accessor function-object-fn
             :initarg :function)))

(defclass expr-object (function-object)
  ())

(defun mk-expr (fn)
  (make-instance 'expr-object :function fn))

(defclass fixed-object (function-object)
  ())

(defun mk-fixed (fn)
  (make-instance 'fixed-object :function fn))

(defmethod eq-object ((lhs basic-object) (rhs (eql nil)))
  nil)

(defmethod eq-object ((lhs (eql nil)) (rhs basic-object))
  nil)

(defmethod eq-object ((lhs (eql nil)) (rhs (eql nil)))
  t)

(defmethod eq-object ((lhs single-value-object) (rhs single-value-object))
  (equal (object-value lhs) (object-value rhs)))

(defmethod eq-object ((lhs list-object) (rhs list-object))
  (eq-tree (list-object-elements lhs) (list-object-elements rhs)
           :test #'eq-object))

(defmethod maru-nil? ((object list-object))
  (eq-object object (mk-list)))

(defmethod maru-nil? ((object basic-object))
  nil)

;;; sexpr : should be a (possibly nested) list of string literals
(defun untype-everything (sexpr)
  (tree-map #'(lambda (string) (mk-untyped string)) sexpr))

(defmethod inform ((object untyped-object)
                   (transformer-name (eql 'type))
                   (whatami (eql 'arg)))
  (declare (special *ctx*))
  (let* ((val (object-value object))
         (len (length val))
         (first-char (char val 0)))
    (cond ((char= #\" first-char)                   ; string
           (cons nil (mk-string (subseq val 1 (1- len)))))
          ((alpha-char-p first-char) (cons nil (maru-intern *ctx* val)))
          ((digit-char-p first-char)
           (cons nil
                 (if (and (>= len 2) (char-equal #\x (char val 1)))
                     (progn
                       (assert (> len 2))
                       (mk-number (subseq val 2 len) :hex t))
                     (mk-number val))))
          ((char= #\? first-char)
           (cons nil (mk-char (char val 1))))
          (t (error "unsure how to do type conversion")))))

(defmethod inform ((object untyped-object)
                   (transformer-name (eql 'type))
                   (whatami (eql 'lead)))
  t)

(defmethod pass ((object untyped-object)
                 (transformer-name (eql 'type))
                 (args list))
  (declare (special *ctx*))
  (cons nil (append (list (maru-intern *ctx* (object-value object)))
                    args)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;  maru evalutator transformer
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; > hardcoded semantics for evaluation composition

;; FIXME: implement
(defun applicator-from-internal (type)
  (declare (ignore type))
  nil)

;;;;;;;;;; basic object ;;;;;;;;;;
; > use *applicators*

;; if a type does not have a specific evaluation semantic; it just
;; evaluates to itself
(defmethod inform ((object basic-object)
                   (transformer-name (eql 'eval))
                   (whatami (eql 'arg)))
  `(nil . ,object))

(defmethod inform :around ((object basic-object)
                           (transformer-name (eql 'eval))
                           (whatami (eql 'arg)))
  (cond ((applicator-from-internal (type-of object))
         (error "args shouldn't get messages when there is an applicator"))
        (t (assert (next-method-p)) (call-next-method))))

(defmethod inform ((object basic-object)
                   (transformer-name (eql 'eval))
                   (whatami (eql 'lead)))
  (error (format nil "implement eval inform for ~A lead~%"
                 (type-of object))))

(defmethod inform :around ((object basic-object)
                           (transformer-name (eql 'eval))
                           (whatami (eql 'lead)))
  (cond ((applicator-from-internal (type-of object)) nil)
         (t (assert (next-method-p)) (call-next-method))))

(defmethod pass ((object basic-object)
                 (trasformer-name (eql 'eval))
                 (args list))
  (error (format nil "implement eval pass for ~A~%"
                 (type-of object))))

;; FIXME: implement
(defmethod pass :around ((object basic-object)
                         (transformer-name (eql 'eval))
                         (args list))
  (let ((applicator (applicator-from-internal (type-of object))))
    (cond (applicator (error "call the applicator and pass args!"))
          (t (assert (next-method-p)) (call-next-method)))))

;;;;;;;;;; symbol object ;;;;;;;;;;

(defmethod inform ((object symbol-object)
                   (transformer-name (eql 'eval))
                   (whatami (eql 'arg)))
  (declare (special *ctx*))
  (let ((binding (maru-lookup *ctx* object)))
    (if binding
        `(nil . ,binding)
        (error (format nil "arg ~A is undefined" (object-value object))))))

(defmethod inform ((object symbol-object)
                   (transformer-name (eql 'eval))
                   (whatami (eql 'lead)))
  t)

(defmethod pass ((object symbol-object)
                 (transformer-name (eql 'eval))
                 (args list))
  (declare (special *ctx*))
  (let ((binding (maru-lookup *ctx* object)))
    (if binding
        (pass binding 'eval args)
        (error (format nil "~A is undefined" (object-value object))))))

;;;;;;;;;; function object ;;;;;;;;;;

(defmethod inform ((object expr-object)
                   (transformer-name (eql 'eval))
                   (whatami (eql 'arg)))
  object)

(defmethod inform ((object expr-object)
                   (transformer-name (eql 'eval))
                   (whatami (eql 'lead)))
  t)

(defmethod pass ((object expr-object)
                 (transformer-name (eql 'eval))
                 (args list))
  (declare (special *ctx*))
  (let ((fn (function-object-fn object)))
    `(nil . ,(apply fn *ctx* args))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;            Tests
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun name-to-fn (name)
  (symbol-function (find-symbol (string-upcase name))))

(let ((tests '()))
  (defun add-test (name)
    (setf tests (cons name tests)))
  (defun test ()
    (let ((fails (reduce (lambda (bads e)
                           (if (funcall (name-to-fn e))
                               bads
                               (cons e bads)))
                          tests
                          :initial-value '()))
          (total (length tests)))
      (format t "Test score: ~A/~A~%" (- total (length fails)) total)
      (format t "Failing tests: ~A~%" fails))))

(defmacro deftest (name &rest body)
  (add-test (symbol-name name))
 `(defun ,name ()
    ,@body))

(deftest test-whitespace
  (and (whitespace? #\Backspace) (whitespace? #\Newline)
       (not (whitespace? #\a)) (not (whitespace? #\$))))

(deftest test-next-char-factory
  (let ((next-char-fn (next-char-factory "world!")))
    (and (char= (funcall next-char-fn) #\w)
         (char= (funcall next-char-fn) #\o)
         (progn
           (funcall next-char-fn 'unread)
           (funcall next-char-fn 'unread)
           (char= (funcall next-char-fn) #\w))
         (progn
           (char= (funcall next-char-fn) #\o))
         (progn
           (funcall next-char-fn 'unread)
           (funcall next-char-fn 'unread)
           (funcall next-char-fn 'unread)
           (string= (funcall next-char-fn) 'negative-space))
         (char= (funcall next-char-fn) #\w)
         (char= (funcall next-char-fn) #\o)
         (char= (funcall next-char-fn) #\r)
         (char= (funcall next-char-fn) #\l)
         (progn
           (funcall next-char-fn 'unread)
           (char= (funcall next-char-fn) #\l))
         (char= (funcall next-char-fn) #\d))))

(deftest test-next-char-factory-peek
  (let ((next-char-fn (next-char-factory "sometext")))
    (and (char= (funcall next-char-fn) #\s)
         (char= (funcall next-char-fn 'peek) #\o)
         (char= (funcall next-char-fn 'peek) #\o)
         (char= (funcall next-char-fn) #\o)
         (char= (funcall next-char-fn 'peek) #\m)
         (progn
           (funcall next-char-fn 'unread)
           (char= (funcall next-char-fn 'peek) #\o)))))

(deftest test-tokenize-parenlist
  (let ((next-char-fn (next-char-factory "(big fast (cars) are fast)")))
    (and (equal (tokenize-parenlist next-char-fn nil)
                '("big" "fast" ("cars") "are" "fast")))))

(deftest test-tokenize-characters
  (let ((next-char-fn (next-char-factory "only the first")))
    (and (equal (tokenize-characters next-char-fn) "only")
         (equal (tokenize-characters next-char-fn) "the")
         (equal (tokenize-characters next-char-fn) "first")
         (equal (tokenize-characters next-char-fn) ""))))

(deftest test-tokenize-characters-paren-bug
  (let ((next-char-fn (next-char-factory "some-expr)")))
    (and (equal (tokenize-characters next-char-fn) "some-expr")
         (char= (funcall next-char-fn 'peek) #\))
         (equal (tokenize-characters next-char-fn) "")
         (equal (tokenize-characters next-char-fn) ""))))

(deftest test-simple-tokenize
  (let ((next-char-fn (next-char-factory "tokenize this plz")))
    (and (equal (tokenize next-char-fn) "tokenize")
         (equal (tokenize next-char-fn) "this")
         (equal (tokenize next-char-fn) "plz"))))

(deftest test-remove-trailing-paren
  (let ((next-char-fn-1 (next-char-factory "   )A"))
        (next-char-fn-2 (next-char-factory ")B")))
    (and (progn
           (remove-trailing-paren next-char-fn-1)
           (char= (funcall next-char-fn-1) #\A))
         (progn
           (remove-trailing-paren next-char-fn-2)
           (char= (funcall next-char-fn-2) #\B)))))

(deftest test-untype-everything
  (let ((next-char-fn
          (next-char-factory " (this (should (be ) untyped) )"))
        (output (list (mk-untyped "this") (list (mk-untyped "should")
                                                (list (mk-untyped "be"))
                                                (mk-untyped "untyped")))))
    (eq-tree (untype-everything (tokenize next-char-fn)) output
             :test #'eq-object)))

(deftest test-noop-transform
  (let ((noop-transformer (make-transformer :name 'noop))
        (untyped-expr (untype-everything
                        (tokenize
                          (next-char-factory "(1 2 3 4 5)")))))
    (eq-tree (transform noop-transformer untyped-expr nil) untyped-expr
             :test #'eq-object)))

(deftest test-unquote-handler
  (let ((next-char-fn
          (next-char-factory ",something")))
    (funcall next-char-fn)
    (equal (unquote-handler next-char-fn nil)
           '("unquote" "something"))))

(deftest test-desugar
  (let ((next-char-fn
          (next-char-factory "(this ,@(is text) ,so is ,,this)"))
        (read-table '((#\, . unquote-handler))))
    (equal (tokenize next-char-fn read-table)
           '("this" ("unquote-splicing" ("is" "text")) ("unquote" "so")
             "is" ("unquote" ("unquote" "this"))))))

(deftest test-next-char-factory-peek-bug
  (let ((next-char-fn
          (next-char-factory "something")))
    (progn (equal (funcall next-char-fn) #\s)
         (equal (funcall next-char-fn 'peek) #\o)
         (equal (funcall next-char-fn 'peek) #\o)
         (equal (funcall next-char-fn) #\o))))

(deftest test-type-transformer
  (let ((type-transformer (make-transformer :name 'type))
        (untyped-expr (untype-everything
                        (tokenize
                          (next-char-factory
                            "(some-fn a-sym (more here) sym9001)"))))
        (typed-expr (list (mk-symbol "some-fn")
                          (mk-symbol "a-sym")
                          (list (mk-symbol "more") (mk-symbol "here"))
                          (mk-symbol "sym9001")))
        (ctx (maru-mk-ctx)))
    (eq-tree (transform type-transformer untyped-expr ctx) typed-expr
             :test #'eq-object)))

(deftest test-type-transformer-number
  (let ((type-transformer (make-transformer :name 'type))
        (untyped-expr (untype-everything
                        (tokenize
                          (next-char-factory
                            "(trees 0x123 (green 2) 0X456)"))))
        (typed-expr (list (mk-symbol "trees") (mk-number "123" :hex t)
                          (list (mk-symbol "green") (mk-number "2"))
                          (mk-number "456" :hex t)))
        (ctx (maru-mk-ctx)))
    (eq-tree (transform type-transformer untyped-expr ctx) typed-expr
             :test #'eq-object)))

(deftest test-type-transform-char-and-string
  (let ((type-transformer (make-transformer :name 'type))
        (untyped-expr (untype-everything
                        (tokenize
                          (next-char-factory
                            "(running \"man\" ?r (u ?n \"s\") ?!)"))))
        (typed-expr
          (list (mk-symbol "running") (mk-string "man") (mk-char #\r)
                (list (mk-symbol "u") (mk-char #\n) (mk-string "s"))
                (mk-char #\!)))
        (ctx (maru-mk-ctx)))
    (eq-tree (transform type-transformer untyped-expr ctx) typed-expr
             :test #'eq-object)))

(deftest test-maru-intern
  (let* ((ctx (maru-mk-ctx))
         (out-sym (mk-symbol "hello-world"))
         (test-sym nil))
    (setf test-sym (maru-intern ctx "hello-world"))
    (and (eq-object test-sym out-sym)
         (member out-sym (maru-context-symbols ctx) :test 'eq-object)
         (= 1 (length (maru-context-symbols ctx)))
         (= 0 (length (maru-env-bindings (maru-context-env ctx)))))))

(deftest test-intern-symbols-when-typing
  (let ((type-transformer (make-transformer :name 'type))
        (untyped-expr (untype-everything
                        (tokenize
                          (next-char-factory
                            "(type these (symbols 123) \"please\" kk)"))))
        (ctx (maru-mk-ctx))
        (out nil))
    (setf out (transform type-transformer untyped-expr ctx))
    (and (= 0 (length (maru-env-bindings (maru-context-env ctx))))
         (null (maru-env-parent (maru-context-env ctx)))
         (= 4 (length (maru-context-symbols ctx)))
         (member (mk-symbol "type") (maru-context-symbols ctx)
                 :test #'eq-object)
         (member (mk-symbol "these") (maru-context-symbols ctx)
                 :test #'eq-object)
         (member (mk-symbol "symbols") (maru-context-symbols ctx)
                 :test #'eq-object)
         (not (member (mk-symbol "123") (maru-context-symbols ctx)
                 :test #'eq-object))
         (not (member (mk-symbol "please") (maru-context-symbols ctx)
                 :test #'eq-object))
         (member (mk-symbol "kk") (maru-context-symbols ctx)
                 :test #'eq-object))))

(deftest test-maru-define
  (let* ((ctx (maru-mk-ctx))
         (obj (mk-number "4001"))
         (sym-string "neverneverneverland")
         (test-out (cons (mk-symbol sym-string) obj))
         (out nil))
    (setf out (maru-define ctx (maru-intern ctx sym-string) obj))
    (and (eq-object (car out) (car test-out))
         (eq-object (cdr out) (cdr test-out))
         (= 1 (length (maru-context-symbols ctx)))
         (= 1 (length (maru-env-bindings (maru-context-env ctx)))))))

(deftest test-maru-lookup
  (let* ((ctx (maru-mk-ctx :parent (make-instance 'maru-env
                                     :bindings nil
                                     :parent nil)))
         (obj (mk-number "43"))
         (sym "some-symbol")
         (obj2 (mk-string "thisandthat"))
         (sym2 "another-symbol")
         (obj3 (mk-string "ballll"))
         (sym3 "in")
         (s3 nil)
         (doesntexist (maru-intern ctx "blahblah")))
    (maru-define ctx (maru-intern ctx sym) obj)
    (maru-define ctx (maru-intern ctx sym2) obj2)

    (setf s3 (maru-intern ctx sym3))
    (maru-define (maru-parent-ctx ctx) s3 obj3)

    (and (eq-object obj (maru-lookup ctx (mk-symbol sym)))
         (eq nil (maru-lookup (maru-parent-ctx ctx) (mk-symbol sym)))
         (eq-object obj2 (maru-lookup ctx (mk-symbol sym2)))
         (eq nil (maru-lookup (maru-parent-ctx ctx) (mk-symbol sym2)))
         (eq-object obj3 (maru-lookup ctx (mk-symbol sym3)))
         (eq-object obj3
                    (maru-lookup (maru-parent-ctx ctx) (mk-symbol sym3)))
         (eq nil (maru-lookup ctx doesntexist))
         (eq nil (maru-lookup (maru-parent-ctx ctx) doesntexist)))))

(deftest test-initialize-simple-maru
  (let ((ctx (maru-initialize)))
    (and (maru-lookup ctx (mk-symbol "if"))
         (maru-lookup ctx (mk-symbol "cons"))
         (maru-lookup ctx (mk-symbol "car"))
         (maru-lookup ctx (mk-symbol "cdr"))
         (not (maru-lookup ctx (mk-symbol "t")))
         (member (mk-symbol "t") (maru-context-symbols ctx)
                 :test #'eq-object))))

(deftest test-maru-primitive-cons
  (let* ((ctx (maru-initialize))
         (a (mk-string "this"))
         (b (mk-number "200"))
         (out nil))
    (setf out
          (funcall (function-object-fn
                     (maru-lookup ctx (maru-intern ctx "cons")))
                   ctx a b))
    (and (eq-object a (car out))
         (eq-object b (cdr out)))))

(deftest test-maru-eval-transform-simple
  (let* ((ctx (maru-initialize))
         (eval-transformer (make-transformer :name 'eval))
         (untyped-expr (untype-everything
                         (tokenize
                           (next-char-factory "(cons \"kewl\" 22)"))))
         (type-transformer (make-transformer :name 'type))
         (typed-expr (transform type-transformer untyped-expr ctx))
         (out nil))
    (setf out (transform eval-transformer typed-expr ctx))
    (and (eq-object (car out) (mk-string "kewl"))
         (eq-object (cdr out) (mk-number "22")))))

(deftest test-maru-eval-transform-simple-bindings
  (let* ((ctx (maru-initialize))
         (eval-transformer (make-transformer :name 'eval))
         (untyped-expr (untype-everything
                         (tokenize
                           (next-char-factory
                             "(cons kewl (cons yessuh 22))"))))
         (type-transformer (make-transformer :name 'type))
         (typed-expr (transform type-transformer untyped-expr ctx))
         (out nil))
    (maru-define ctx (mk-symbol "yessuh") (mk-number "100"))
    (maru-define ctx (mk-symbol "kewl") (mk-string "astronauts"))
    (setf out (transform eval-transformer typed-expr ctx))
    (and (eq-object (car out)  (mk-string "astronauts"))
         (eq-object (cadr out) (mk-number "100"))
         (eq-object (cddr out)  (mk-number "22")))))

(deftest test-maru-primitive-if-simple
  (let ((ctx (maru-initialize)))
         ;; test 'then' branch
    (and (eq-object (mk-string "goodbye")
                    (funcall (function-object-fn
                               (maru-lookup ctx (mk-symbol "if")))
                             ctx
                             (mk-string "not-nil")      ;; predicate
                             (mk-string "goodbye")      ;; then
                             (mk-number "100")))        ;; else
         ;; test 'else' branch
         (eq-object (mk-number "14")
                    (funcall (function-object-fn
                                (maru-lookup ctx (maru-intern ctx "if")))
                             ctx
                             (mk-list)                  ;; predicate
                             (mk-number "12")           ;; then
                             (mk-number "14"))))))      ;; else

(deftest test-maru-primitive-if
  nil)
#|
  (let ((ctx (maru-initialize)))
    (and (equal 2 (funcall (lookup ctx 'if) '(1 2 3) ctx))
         (equal 4 (funcall (lookup ctx 'if) '(() 12 4) ctx))
         (equal "str" (funcall (lookup ctx 'if) '(t "str") ctx))
         (equal '() (funcall (lookup ctx 'if) '(() "other") ctx)))))
|#

(deftest test-applicator-from-internal
  "should be able to take an applicator and get it's internal function"
  nil)


