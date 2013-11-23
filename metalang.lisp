;;;; library for defining language semantics
;;;; Aaron Burrow : burrows.labs@gmail.com

;;;; components
;;;; > tokenizer, produces sexpressions from a string literal
;;;; > translation manager, translations against sexpressions

;;;; TODO
;;;; > How do we want to handle lists? Do we want to support eval_pair
;;;;   like behavior in our infrastructure? Does it even make sense in
;;;;   our model?
;;;;   + ((do-something 1 2) 3 4)   ; must send message to list form
;;;;   + ()                         ; indiciates not true
;;;; > Determine the best way to consolidate default behaviors in
;;;;   transformations.
;;;; > write macros to cleanup maru initialization
;;;;   + arithmetic
;;;; > *applicators*, *expanders*
;;;;
;;;; NOTES
;;;; . forwarding dispatches to symbol objects (because things that
;;;;   are relevant to a transformation (ie macros) are binded to
;;;;   symbols) hides intent to some extent?
;;;;   > for traditional sexpression languages where must application
;;;;     is done by looking up the symbol then composing on it's binding
;;;;     this is a very prominent feature; how should it be encoded?
;;;; . quote handling
;;;;   > the transformers use common lisp lists (and not maru lisps) to
;;;;     represent maru code. this means that 'quote' must do some type
;;;;     of runtime conversion into a maru list.

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
        ; push empty lists but not empty strings (whitespace)
        (unless (and (typep e 'string) (zerop (length e)))
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

(defun quote-handler (next-char-fn read-table)
  (let ((quoted (tokenize next-char-fn read-table)))
    (list "quote" quoted)))

(defun quasiquote-handler (next-char-fn read-table)
  (let ((quoted (tokenize next-char-fn read-table)))
    (list "quasiquote" quoted)))

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

(defun nice-eval (expr &key _ctx _tfuncs)
  (declare (special *ctx* *tfuncs*))
  (let ((ctx (if _ctx _ctx *ctx*))
        (tfuncs (if _tfuncs _tfuncs *tfuncs*)))
    (assert (and expr ctx tfuncs))
    (transform (make-transformer :name 'eval)
               expr
               ctx
               :tfuncs tfuncs)))

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

;;;;; transformer psuedo-list ;;;;;

;;; begin magic
(defmacro defsugar (name)
  (let ((special-name 
          (intern (string-upcase (scat "*" (string name) "*")))))
    `(defun ,name (&rest args)
       (declare (special ,special-name))
       (assert ,special-name)
       (apply ,special-name args))))

(defstruct tfuncs
  car cdr cons null nil atom listp)

(declaim (special *tcar* *tcdr* *tcons* *tnull*
                  *tnil* *tatom* *tlistp*))

(defmacro let-sugar (tfuncs &rest body)
  `(let ((*tcar* (tfuncs-car ,tfuncs))   (*tcdr* (tfuncs-cdr ,tfuncs))
         (*tcons* (tfuncs-cons ,tfuncs)) (*tnull* (tfuncs-null ,tfuncs))
         (*tnil* (tfuncs-nil ,tfuncs))   (*tatom* (tfuncs-atom ,tfuncs))
         (*tlistp* (tfuncs-listp ,tfuncs)))
     ,@body))

(defsugar tcar)
(defsugar tcdr)
(defsugar tcons)
(defsugar tnull)
(defsugar tnil)
(defsugar tatom)
(defsugar tlistp)

(defun std-nil ()
  nil)

(defun std-tfuncs ()
  (make-tfuncs :car   #'car
               :cdr   #'cdr
               :cons  #'cons
               :null  #'null
               :nil   #'std-nil
               :atom  #'atom
               :listp #'listp))

(defun tlength (tlist)
  (cond ((tnull tlist) 0)
        (t (1+ (tlength (tcdr tlist))))))

(defun tmapcar (fn tlist)
  (cond ((tnull tlist) (tnil))
        (t (tcons (funcall fn (tcar tlist))
                  (tmapcar fn (tcdr tlist))))))

;; this function should never be used if the args are still internal typed
(defun tapply-with-context (fn ctx args)
  (assert (typep args 'list-object))
  (funcall fn ctx args))

(defun back-talk-arg (transformer expr)
  (declare (special *ctx*))
  (assert (tatom expr))
  ;; response : (transform-more? . sexpr)
  (let ((response (inform expr (transformer-name transformer) 'arg)))
    (if (car response)
        (transform transformer (cdr response) *ctx*)
        (cdr response))))

(defun back-talk-sexpr (transformer lead &key expr-args)
  (declare (special *ctx* *tfuncs*))
  (assert (tlistp expr-args))
  ;; response : can-i-talk-to-your-arguments?
  (let* ((response (inform lead (transformer-name transformer) 'lead))
         (args (tmapcar #'(lambda (a)
                            (if response
                                (transform transformer
                                           a
                                           *ctx*
                                           :tfuncs *tfuncs*)
                                (identity a)))
                        expr-args)))
      ;; response : (transform-more? . sexpr)
      (let ((response-2
              (pass lead (transformer-name transformer) args)))
        (if (car response-2)
            (transform transformer (cdr response-2) *ctx*)
            (cdr response-2)))))

;;; transform a single expression {sexpression, atom}
(defun transform (transformer expr ctx &key (tfuncs (std-tfuncs)))
  (let-sugar tfuncs
    (let ((*ctx* ctx)
          (*tfuncs* tfuncs))    ; necessary for recursive calls
      (declare (special *ctx* *tfuncs*))
      (cond ((tnull expr) (tnil))
            ((tatom expr)
             (back-talk-arg transformer expr))
            (t
              (back-talk-sexpr transformer
                               (tcar expr)
                               :expr-args (tcdr expr)))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;            maru
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defclass maru-env ()
  ((bindings :accessor maru-env-bindings
             :initarg  :bindings
             :initform (list (cons (mk-symbol "dummy")
                                   (mk-symbol "dummyvalue"))))
   (parent :accessor  maru-env-parent
           :initarg   :parent
           :initform  nil
           :type      maru-env)))

(defstruct maru-context
  (env (make-instance 'maru-env))
  (symbols (list (mk-symbol "dummy-so-prepend-doesnt-break"))))  ; hack

(defun maru-mk-ctx (&key parent-ctx)
  (if parent-ctx
      (make-maru-context :env (make-instance 'maru-env
                                :parent (maru-context-env parent-ctx))
                         :symbols (maru-context-symbols parent-ctx))
      (make-maru-context)))

;; for testing
(defun maru-parent-ctx (ctx)
  (let ((new-ctx (copy-structure ctx)))
    (setf (maru-context-env new-ctx)
          (maru-env-parent (maru-context-env ctx)))
    new-ctx))

(defun maru-root-env (ctx)
  (assert (typep ctx 'maru-context))
  (labels ((do-work (env)
             (let ((parent (maru-env-parent env)))
               (cond ((null parent) env)
                     (t (do-work parent))))))
    (do-work (maru-context-env ctx))))

(defun maru-intern (ctx text)
  (let ((symbol (mk-symbol text)))
    (car (prepend symbol (maru-context-symbols ctx)))))

;;; always adds things to the root environment
(defun maru-define (ctx symbol obj)
  (assert (typep symbol 'symbol-object))
  ;; if the symbol hasn't been internd, we can't use it
  (unless (member symbol (maru-context-symbols ctx) :test #'eq-object)
    (error "``~A'' has not been internd" (object-value symbol)))
  (let ((root-env (maru-root-env ctx)))
    (car (prepend `(,symbol . ,obj) (maru-env-bindings root-env)))))

;;; for defining non-root bindings (lambda + let)
(defun maru-define-new-binding (ctx symbol obj)
  (assert (typep symbol 'symbol-object))
  (car (push (cons symbol obj)
             (maru-env-bindings (maru-context-env ctx)))))

(defun maru-lookup-raw (ctx symbol)
  (labels ((l-up (env)
             (when (null env)
               (return-from l-up nil))
             (let ((bins (maru-env-bindings env)))
               (cond ((assoc symbol bins :test #'eq-object)
                      (assoc symbol bins :test #'eq-object))
                     (t (l-up (maru-env-parent env)))))))
    (l-up (maru-context-env ctx))))

(defun maru-lookup (ctx symbol)
  (unless (member symbol (maru-context-symbols ctx) :test #'eq-object)
    (error (format nil "symbol '~A' has not been interned!"
                       (object-value symbol))))
  (let ((pair (maru-lookup-raw ctx symbol)))
    (if pair (cdr pair) nil)))

(defun maru-boolean-cmp (lhs rhs fn)
  (when (not (and (typep lhs 'number-object) (typep rhs 'number-object)))
    (return-from maru-boolean-cmp (mk-bool nil)))
  (mk-bool (funcall fn (object-value lhs) (object-value rhs))))

(defgeneric maru-printable-object (object)
  (:method ((object untyped-object))
    (scat "<untyped ``" (object-value object) "'' >"))
  (:method ((object nil-object))
    "<nil>")
  (:method ((object single-value-object))
    (object-value object))
  (:method ((object function-object))
    "<generic-function-object>")
  (:method ((object runtime-closure-object))
    "<runtime-closure-object>")
  (:method ((object form-object))
    "<form-object>")
  (:method ((object pair-object))
    (scat "("
          (maru-printable-object (pair-object-car object))
          " . "
          (maru-printable-object (pair-object-cdr object))
          ")")))

(defun maru-printable (sexpr)
  (tree-map #'maru-printable-object sexpr))

(defgeneric maru-atom? (object)
  (:method ((object pair-object))
    nil)
  (:method ((object basic-object))
    t))

(defgeneric maru-list? (object)
  (:method ((object nil-object))
    t)
  (:method ((object pair-object))
    t)
  (:method (object)
    nil))

(defun maru-tfuncs ()
  (make-tfuncs :car   #'maru-car
               :cdr   #'maru-cdr
               :cons  #'mk-pair
               :null  #'maru-nil?
               :nil   #'maru-nil
               :atom  #'maru-atom?
               :listp #'maru-list?))

;;; > intern primitives and add their bindings to global env
;;; > add runtime compositioners
;;;     + *expanders*   : []
;;;     + *evaluators*  : [eval-symbol]
;;;     + *applicators* : [apply-fixed, apply-expr]
(defun maru-initialize ()
  (let ((ctx (maru-mk-ctx)))
    ;; primitives
    (maru-define ctx (maru-intern ctx "quote")
                     (mk-fixed #'maru-primitive-quote))
    (maru-define ctx (maru-intern ctx "if")
                     (mk-fixed #'maru-primitive-if))
    (maru-intern ctx "t")
    (maru-define ctx (maru-intern ctx "cons")
                     (mk-expr #'maru-primitive-cons))
    (maru-define ctx (maru-intern ctx "car")
                     (mk-expr #'maru-primitive-car))
    (maru-define ctx (maru-intern ctx "set-car")
                     (mk-expr #'maru-primitive-set-car))
    (maru-define ctx (maru-intern ctx "cdr")
                     (mk-expr #'maru-primitive-cdr))
    (maru-define ctx (maru-intern ctx "set-cdr")
                     (mk-expr #'maru-primitive-set-cdr))
    (maru-define ctx (maru-intern ctx "caar")
                     (mk-expr #'maru-primitive-caar))
    (maru-define ctx (maru-intern ctx "and")
                     (mk-fixed #'maru-primitive-and))
    (maru-define ctx (maru-intern ctx "define")
                     (mk-fixed #'maru-primitive-define))
    ;; extension
    (maru-define ctx (maru-intern ctx "block")
                     (mk-expr #'maru-primitive-block))
    (maru-define ctx (maru-intern ctx "lambda")
                     (mk-fixed #'maru-primitive-lambda))
    (maru-define ctx (maru-intern ctx "let")
                     (mk-fixed #'maru-primitive-let))
    (maru-define ctx (maru-intern ctx "while")
                     (mk-fixed #'maru-primitive-while))
    (maru-define ctx (maru-intern ctx "+")
                     (mk-expr #'maru-primitive-add))
    (maru-define ctx (maru-intern ctx "-")
                     (mk-expr #'maru-primitive-sub))
    (maru-define ctx (maru-intern ctx "*")
                     (mk-expr #'maru-primitive-mul))
    (maru-define ctx (maru-intern ctx "/")
                     (mk-expr #'maru-primitive-div))
    (maru-define ctx (maru-intern ctx "=")
                     (mk-expr #'maru-primitive-eq))
    (maru-define ctx (maru-intern ctx "!=")
                     (mk-expr #'maru-primitive-neq))
    (maru-define ctx (maru-intern ctx "<")
                     (mk-expr #'maru-primitive-lt))
    (maru-define ctx (maru-intern ctx "<=")
                     (mk-expr #'maru-primitive-lte))
    (maru-define ctx (maru-intern ctx ">")
                     (mk-expr #'maru-primitive-gt))
    (maru-define ctx (maru-intern ctx ">=")
                     (mk-expr #'maru-primitive-gte))
    (maru-define ctx (maru-intern ctx "set")
                     (mk-form #'maru-primitive-set))
    (maru-define ctx (maru-intern ctx "seth")
                     (mk-fixed #'maru-primitive-seth))
    (maru-define ctx (maru-intern ctx "pair?")
                     (mk-expr #'maru-primitive-pair?))
    ;; extension
    (maru-define ctx (maru-intern ctx "list")
                     (mk-expr #'maru-primitive-list))
    ;; strings
    (maru-define ctx (maru-intern ctx "string")
                     (mk-expr #'maru-primitive-string))
    (maru-define ctx (maru-intern ctx "string-length")
                     (mk-expr #'maru-primitive-string-length))
    (maru-define ctx (maru-intern ctx "string-at")
                     (mk-expr #'maru-primitive-string-at))
    (maru-define ctx (maru-intern ctx "set-string-at")
                     (mk-expr #'maru-primitive-set-string-at))

    (maru-define ctx (maru-intern ctx "form")
                     (mk-expr #'maru-primitive-form))

    ;; compositioners
    (maru-define ctx (maru-intern ctx "*expanders*") (mk-array 32))
    (maru-define ctx (maru-intern ctx "*evaluators*") (mk-array 32))
    (maru-define ctx (maru-intern ctx "*applicators*") (mk-array 32))

    ctx))

(defun maru-eval (ctx expr)
  (declare (ignore ctx expr))
  nil)

(defun binding-exists? (ctx sym)
  (let ((symbol (mk-symbol sym)))
    (and (maru-lookup ctx symbol)
         (member symbol (maru-context-symbols ctx) :test #'eq-object))))

(defun maru-spawn-child-env (ctx)
  (maru-mk-ctx :parent-ctx ctx))

(defun internal-list-to-maru-list (list)
  (assert (listp list))
  (cond ((null list) (maru-nil))
        ((listp (car list))
         (mk-pair (internal-list-to-maru-list (car list))
                  (internal-list-to-maru-list (cdr list))))
        (t (mk-pair (car list) (internal-list-to-maru-list (cdr list))))))

(defun maru-list-to-internal-list (maru-list)
  (assert (maru-list? maru-list))
  (cond ((maru-nil? maru-list) '())
        ((maru-atom? (maru-car maru-list))
         (cons (maru-car maru-list)
               (maru-list-to-internal-list (maru-cdr maru-list))))
        (t (cons (maru-list-to-internal-list (maru-car maru-list))
                 (maru-list-to-internal-list
                   (maru-cdr maru-list))))))

(defun maru-list-to-internal-list-1 (maru-list)
  (assert (maru-list? maru-list))
  (cond ((maru-nil? maru-list) '())
        (t (cons (maru-car maru-list)
                 (maru-list-to-internal-list-1 (maru-cdr maru-list))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;      maru primitives
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; expr
(defun maru-primitive-quote (ctx args)
  (declare (ignore ctx))
  (assert (= 1 (maru-length args)))
  (maru-car args))

; fixed
(defun maru-primitive-if (ctx args)
  (declare (ignore ctx))
  (assert (= 3 (maru-length args)))
  (let ((test (maru-car  args))
        (then (maru-cadr args))
        (else (maru-cdr  (maru-cdr args))))
    (if (not (maru-nil? (nice-eval test)))
        (nice-eval then)
        (let ((out nil))
          ; implicit block
          (dolist (e (maru-list-to-internal-list-1 else) out)
            (setf out (nice-eval e)))))))

; expr
(defun maru-primitive-cons (ctx args)
  (declare (ignore ctx))
  (assert (= 2 (tlength args)))
  (mk-pair (maru-car args)
           (maru-cadr args)))

; expr
(defun maru-primitive-car (ctx args)
  (declare (ignore ctx))
  (assert (and (= 1 (maru-length args))
               (typep (maru-car args) 'pair-object)))
  (maru-car (maru-car args)))

; expr
(defun maru-primitive-set-car (ctx args)
  (declare (ignore ctx))
  (assert (= 2 (maru-length args)))
  (setf (pair-object-car (maru-car args)) (maru-cadr args)))

; expr
(defun maru-primitive-cdr (ctx args)
  (declare (ignore ctx))
  (assert (and (= 1 (maru-length args))
               (typep (maru-car args) 'pair-object)))
  (maru-cdr (maru-car args)))

; expr
(defun maru-primitive-set-cdr (ctx args)
  (declare (ignore ctx))
  (assert (= 2 (maru-length args)))
  (setf (pair-object-cdr (maru-car args)) (maru-cadr args)))

; expr
(defun maru-primitive-caar (ctx args)
  (declare (ignore ctx))
  (assert (= 1 (maru-length args)))
  (maru-car (maru-car (maru-car args))))

; fixed
(defun maru-primitive-and (ctx args)
  (declare (ignore ctx))
  (let ((out (mk-symbol "t")))
    (dolist (pred (maru-list-to-internal-list-1 args) out)
      (setf out (nice-eval pred))
      (when (maru-nil? out)
        (return out)))))

; form
; FIXME: Should we be expanding here?
(defun maru-primitive-define (ctx args)
  (cdr
    (maru-define ctx (pair-object-car args)
                     (nice-eval (pair-object-car
                                (pair-object-cdr args))))))

; expr
(defun maru-primitive-block (ctx args)
  (declare (ignore ctx))
  ;; FIXME: should use pair object length fn
  (if (zerop (maru-length args))
      (maru-nil)
      (maru-car (maru-last args))))

; fixed
(defun maru-primitive-lambda (ctx args)
  (mk-closure ctx (mk-list (pair-object-car args)
                           (mk-pair (mk-symbol "block")
                                    (pair-object-cdr args)))))

; fixed
(defun maru-primitive-let (ctx args)
  (let ((child-ctx nil))
    (setf child-ctx (maru-spawn-child-env ctx))
    (dolist (arg-param (maru-list-to-internal-list-1 (maru-car args)))
      (maru-define-new-binding
        child-ctx (maru-car arg-param)
                  (nice-eval (mk-pair
                                (mk-symbol "block")
                                (maru-cdr arg-param)))))
    (nice-eval
      (mk-pair (mk-symbol "block") (maru-cdr args))
      :_ctx child-ctx)))

; fixed
;; FIXME.
(defun maru-primitive-while (ctx args)
  (declare (ignore ctx))
  ;; return nil same as boot-eval.c
  (do ()
      ((maru-nil? (nice-eval (maru-car args))) nil)
    (nice-eval (mk-pair (mk-symbol "block") (maru-cdr args)))))

; expr
(defun maru-primitive-add (ctx args)
  (declare (ignore ctx))
  (mk-number (to-string (+ (object-value (maru-car args))
                           (object-value (maru-cadr args))))))

; expr
(defun maru-primitive-sub (ctx args)
  (declare (ignore ctx))
  (mk-number (to-string (- (object-value (maru-car args))
                           (object-value (maru-cadr args))))))

; expr
(defun maru-primitive-mul (ctx args)
  (declare (ignore ctx))
  (mk-number (to-string (* (object-value (maru-car args))
                           (object-value (maru-cadr args))))))

; expr
(defun maru-primitive-div (ctx args)
  (declare (ignore ctx))
  (mk-number (to-string (floor (object-value (maru-car args))
                               (object-value (maru-cadr args))))))

; expr
(defun maru-primitive-eq (ctx args)
  (declare (ignore ctx))
  (mk-bool (eq-object (maru-car args) (maru-cadr args))))

; expr
(defun maru-primitive-neq (ctx args)
  (declare (ignore ctx))
  (maru-boolean-cmp (maru-car args) (maru-cadr args) #'/=))

; expr
(defun maru-primitive-lt (ctx args)
  (declare (ignore ctx))
  (maru-boolean-cmp (maru-car args) (maru-cadr args) #'<))

; expr
(defun maru-primitive-lte (ctx args)
  (declare (ignore ctx))
  (maru-boolean-cmp (maru-car args) (maru-cadr args) #'<=))

; expr
(defun maru-primitive-gt (ctx args)
  (declare (ignore ctx))
  (maru-boolean-cmp (maru-car args) (maru-cadr args) #'>))

; expr
(defun maru-primitive-gte (ctx args)
  (declare (ignore ctx))
  (maru-boolean-cmp (maru-car args) (maru-cadr args) #'>=))

; form
(defun maru-primitive-set (ctx args)
  (declare (ignore ctx))
  (assert (= 2 (maru-length args)))
  (cond ((maru-list? (maru-car args))
         (mk-pair (mk-symbol (scat "set-"
                                   (object-value (maru-caar args))))
                  (mk-pair (maru-cadar args) (maru-cdr args))))
        (t (mk-pair (mk-symbol "seth") args))))

; fixed
; FIXME: make sure the symbol is actually internd
(defun maru-primitive-seth (ctx args)
  (assert (= 2 (maru-length args)))
  (let ((binding (maru-lookup-raw ctx (maru-car args))))
    (when (null binding)
      (error "``~a'' is undefined thus can not be set" (maru-car args)))
    (setf (cdr binding) (nice-eval (maru-cadr args)))))

; expr
(defun maru-primitive-pair? (ctx args)
  (declare (ignore ctx))
  (mk-bool (typep (maru-car args) 'pair-object)))

; expr
(defun maru-primitive-list (ctx args)
  (declare (ignore ctx))
  args)

; expr
(defun maru-primitive-string (ctx args)
  (declare (ignore ctx))
  (assert (and (= 1 (maru-length args))
               (typep (maru-car args) 'number-object)))
  (mk-string :size (object-value (maru-car args))))

; expr
(defun maru-primitive-string-length (ctx args)
  (declare (ignore ctx))
  (assert (and (= 1 (maru-length args))
               (typep (maru-car args) 'string-object)))
  (mk-number (to-string (string-object-size (maru-car args)))))

; expr
(defun maru-primitive-string-at (ctx args)
  (declare (ignore ctx))
  (assert (and (= 2 (maru-length args))
               (typep (maru-car args) 'string-object)
               (typep (maru-cadr args) 'number-object)))
  (let ((index (object-value (maru-cadr args))))
    (if (and (>= index 0) (< index (string-object-size (maru-car args))))
      (mk-char (elt (object-value (maru-car args)) index))
      (maru-nil))))

; expr
(defun maru-primitive-set-string-at (ctx args)
  (declare (ignore ctx))
  (assert (and (= 3 (maru-length args))
               (typep (maru-car args) 'string-object)
               (typep (maru-cadr args) 'number-object)
               (typep (maru-cadr args) 'number-object)))
  (let ((index (object-value (maru-cadr args)))
        (char (object-value (maru-caddr args))))
    (if (and (>= index 0) (< index (string-object-size (maru-car args))))
      (progn
        (setf (elt (object-value (maru-car args)) index) char)
        (maru-car args))
      (maru-nil))))

; expr
(defun maru-primitive-form (ctx args)
  (declare (ignore ctx))
  (assert (and (= 1 (maru-length args))
               (typep (maru-car args) 'runtime-closure-object)))
  (mk-form (maru-car args)))

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
  ())

(defclass pair-object (list-object)
  ((car :accessor pair-object-car
        :initarg :car)
   (cdr :accessor pair-object-cdr
        :initarg :cdr)))

(defun mk-pair (car cdr)
  (make-instance 'pair-object :car car
                              :cdr cdr))

(defun mk-list (&rest elements)
  (if (zerop (length elements))
      (maru-nil)
      (make-instance 'pair-object :car (car elements)
                                  :cdr (apply #'mk-list (cdr elements)))))

(defgeneric maru-car (pair-object)
  (:method ((pair pair-object))
    (pair-object-car pair))
  (:method ((pair nil-object))
    (maru-nil)))

(defgeneric maru-cdr (pair-object)
  (:method ((pair pair-object))
    (pair-object-cdr pair))
  (:method ((pair nil-object))
    (maru-nil)))

(defmethod maru-cadr (maru-list)
  (maru-car (maru-cdr maru-list)))

(defmethod maru-caar (maru-list)
  (maru-car (maru-car maru-list)))

(defmethod maru-cadar (maru-list)
  (maru-car (maru-cdr (maru-car maru-list))))

(defmethod maru-caddr (maru-list)
  (maru-car (maru-cdr (maru-cdr maru-list))))

(defgeneric maru-length (pair)
  (:method ((pair pair-object))
    (1+ (maru-length (maru-cdr pair))))
  (:method ((n nil-object))
    (declare (ignore n))
    0))

;; FIXME: use defgeneric
(defmethod maru-last ((pair pair-object) &optional (n 1))
  (cond ((= n (maru-length pair)) pair)
        (t (maru-last (maru-cdr pair) n))))

(defmethod maru-last ((nl nil-object) &optional (n 1))
  (declare (ignore n))
  (maru-nil))

;;; NOTE: nil is not a pair
(defclass nil-object (list-object)
  ())

(defun maru-nil ()
  (make-instance 'nil-object))

(defclass number-object (single-value-object)
  ())

(defun mk-number (value &key hex)
  (make-instance 'number-object
                 :value (read-from-string (if hex
                                              (scat "#x" value)
                                              value))))

(defclass string-object (single-value-object)
  ())

;; how many characters can I hold
(defmethod string-object-size ((object string-object))
  (1- (length (object-value object))))

;; how many characters before the first nul
(defmethod string-object-length ((object string-object))
  (let ((len (position #\Nul (object-value object))))
    (if (null len)
        (error "this string is not nul terminated!")
        len)))

;; account for the implicit nul
(defun mk-string (&key value size)
  (when (eq (not value) (not size))
    (error "mk-string takes one of value or size"))
  (if value
      (make-instance 'string-object :value (scat value #\Nul))
      (make-instance 'string-object :value (make-string (1+ size)))))

(defclass char-object (single-value-object)
  ())

(defun mk-char (value)
  (assert (typep value 'standard-char))
  (make-instance 'char-object :value value))

(defclass bool-object (single-value-object)
  ())

(defun mk-bool (value)
  (make-instance 'bool-object :value value))

(defclass array-object (basic-object)
  ((elements :accessor array-object-elements
             :initarg  :elements)))

(defun mk-array (size)
  (make-instance 'array-object :elements (make-array size)))

(defclass runtime-closure-object (basic-object)
  ((src :accessor runtime-closure-object-src
        :initarg  :src)
   (ctx :accessor runtime-closure-object-ctx
        :initarg  :ctx)))

(defun mk-closure (ctx src)
  (make-instance 'runtime-closure-object :ctx ctx :src src))

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

(defclass form-object (function-object)
  ())

(defun mk-form (fn)
  (make-instance 'form-object :function fn))

(defgeneric eq-object (lhs rhs)
  (:method ((lhs single-value-object) (rhs single-value-object))
    (equal (object-value lhs) (object-value rhs)))
  (:method ((lhs string-object) (rhs string-object))
    (and (= (string-object-length lhs) (string-object-length rhs))
         (equal (subseq (object-value lhs) 0 (string-object-length lhs))
                (subseq (object-value rhs) 0 (string-object-length rhs)))))
  (:method ((lhs pair-object) (rhs pair-object))
    (and (eq-object (pair-object-car lhs) (pair-object-car rhs))
         (eq-object (pair-object-cdr lhs) (pair-object-cdr rhs))))
  ;; we don't want to do the pair comparison if the second argument
  ;; is a nil
  (:method ((lhs pair-object) (rhs nil-object))
    nil)
  (:method ((lhs nil-object) (rhs nil-object))
    t)
  (:method ((lhs nil-object) (rhs basic-object))
    nil)
  (:method ((lhs basic-object) (rhs nil-object))
    nil)
  ;; nil is false
  (:method ((lhs nil-object) (rhs bool-object))
    (null (object-value rhs)))
  (:method ((lhs bool-object) (rhs nil-object))
    (null (object-value lhs)))
  ;; catch all
  (:method (lhs rhs)
    nil))
  

(defmethod maru-nil? ((object basic-object))
  (eq-object object (maru-nil)))

;;; sexpr : should be a (possibly nested) list of string literals
(defun untype-everything (sexpr)
  (tree-map #'(lambda (string) (mk-untyped string)) sexpr))

(defun type-it (ctx object)
  (let* ((val (object-value object))
         (len (length val))
         (first-char (char val 0)))
    (cond ((char= #\" first-char)                   ; string
           (mk-string :value (subseq val 1 (1- len))))
          ((digit-char-p first-char)
             (if (and (>= len 2) (char-equal #\x (char val 1)))
               (progn
                 (assert (> len 2))
                 (mk-number (subseq val 2 len) :hex t))
               (mk-number val)))
          ((char= #\? first-char)
           (mk-char (char val 1)))
          ((graphic-char-p first-char) (maru-intern ctx val))
          (t (error "unsure how to do type conversion")))))

(defmethod inform ((object untyped-object)
                   (transformer-name (eql 'type))
                   (whatami (eql 'arg)))
  (declare (special *ctx*))
  `(nil . ,(type-it *ctx* object)))

(defmethod inform ((object untyped-object)
                   (transformer-name (eql 'type))
                   (whatami (eql 'lead)))
  t)

(defmethod pass ((object untyped-object)
                 (transformer-name (eql 'type))
                 (args list))
  (declare (special *ctx*))
  (let ((typed-lead (type-it *ctx* object)))
    `(nil . ,(mk-pair typed-lead (internal-list-to-maru-list args)))))


;;;;;;;;;; list as lead ;;;;;;;;;;

(defmethod inform ((list list)
                   (transformer-name (eql 'type))
                   (whatami (eql 'arg)))
  (error "should never be dispatched on list argument!"))

(defmethod inform ((list list)
                   (transformer-name (eql 'type))
                   (whatami (eql 'lead)))
  t)

(defmethod pass ((list list)
                 (transformer-name (eql 'type))
                 (args list))
  (declare (special *ctx*))
  (let ((type-transformer (make-transformer :name 'type)))
    `(nil . ,(cons (transform type-transformer list *ctx*) args))))


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
         (error "args shouldn't get messages if there is an applicator"))
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
                 (args list-object))
  (error (format nil "implement eval pass for ~A~%"
                 (type-of object))))

;; FIXME: implement
(defmethod pass :around ((object basic-object)
                         (transformer-name (eql 'eval))
                         (args list-object))
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
        (error "can not eval symbol ``~A''; no binding!"
               (object-value object)))))

(defmethod inform ((object symbol-object)
                   (transformer-name (eql 'eval))
                   (whatami (eql 'lead)))
  (declare (special *ctx*))
  (let ((binding (maru-lookup *ctx* object)))
    (if binding
        (inform binding 'eval 'lead)        ; forward
        (error (format nil "'~A' is undefined" (object-value object))))))

;;; OF-NOTE: forwarding
(defmethod pass ((object symbol-object)
                 (transformer-name (eql 'eval))
                 (args list-object))
  (declare (special *ctx*))
  (let ((binding (maru-lookup *ctx* object)))
    (if binding
        (pass binding 'eval args)       ; must forward to actual function
        (error (format nil "'~A' is undefined" (object-value object))))))


;;;;;;;;;; function object ;;;;;;;;;;

(defmethod inform ((object expr-object)
                   (transformer-name (eql 'eval))
                   (whatami (eql 'arg)))
  `(nil . ,object))

(defmethod inform ((object expr-object)
                   (transformer-name (eql 'eval))
                   (whatami (eql 'lead)))
  t)

(defmethod pass ((object expr-object)
                 (transformer-name (eql 'eval))
                 (args list-object))
  (declare (special *ctx*))
  (let ((fn (function-object-fn object)))
    `(nil . ,(tapply-with-context fn *ctx* args))))


;;;;;;;;;; fixed object ;;;;;;;;;;

(defmethod inform ((object fixed-object)
                   (transformer-name (eql 'eval))
                   (whatami (eql 'arg)))
  `(nil . ,object))

(defmethod inform ((object fixed-object)
                   (transformer-name (eql 'eval))
                   (whatami (eql 'lead)))
  nil)

(defmethod pass ((object fixed-object)
                 (transformer-name (eql 'eval))
                 (args list-object))
  (declare (special *ctx*))
  (let ((fn (function-object-fn object)))
    `(nil . ,(tapply-with-context fn *ctx* args))))

;;;;;;;;;; runtime closure object ;;;;;;;;;;

(defmethod inform ((object runtime-closure-object)
                   (transformer-name (eql 'eval))
                   (whatami (eql 'arg)))
  `(nil . ,object))

(defmethod inform ((object runtime-closure-object)
                   (transformer-name (eql 'eval))
                   (whatami (eql 'lead)))
  t)

(defmethod pass ((object runtime-closure-object)
                 (transformer-name (eql 'eval))
                 (args list-object))
  (declare (special *ctx*))
  (let ((child-ctx nil))
    ;; use the lexical env from the closure
    ;; FIXME: should we spawn the child here or in
    ;;        maru-primitive-lambda(...)?
    (setf child-ctx
          (maru-spawn-child-env (runtime-closure-object-ctx object)))
    ;; add arguments/parameters to lexical env
    (dolist (arg-param (zip (maru-list-to-internal-list-1
                              (maru-car
                                   (runtime-closure-object-src object)))
                            (maru-list-to-internal-list-1 args)))
      (maru-define-new-binding
        child-ctx (car arg-param) (cadr arg-param)))
    ;; apply the function in the lexical env
    `(nil . ,(nice-eval (maru-cadr (runtime-closure-object-src object))
                        :_ctx child-ctx))))

;;;;;;;;;; runtime closure object ;;;;;;;;;;

(defmethod inform ((object number-object)
                   (transformer-name (eql 'eval))
                   (whatami (eql 'arg)))
  `(nil . ,object))

(defmethod inform ((object number-object)
                   (transformer-name (eql 'eval))
                   (whatami (eql 'lead)))
  (error "numbers shouldn't be lead!"))

(defmethod pass ((object number-object)
                 (transformer-name (eql 'eval))
                 (args list-object))
  (error "numbers shouldn't be lead!"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;  maru expansion transformer
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; if we are forwarded too from some symbol and we don't have anything
;;; to do during expansion; then we need to evaluate to the symbol not
;;; our value (the binding)
(defparameter *forwarding-symbol* nil)

;;;;;;;;;; basic object ;;;;;;;;;;
;;; > FIXME: should use *expanders*

;; if a type does not have a specific expansion semantic; it just
;; evaluates to itself
(defmethod inform ((object basic-object)
                   (transformer-name (eql 'expand))
                   (whatami (eql 'arg)))
  (declare (special *forwarding-symbol*))
  (if *forwarding-symbol*
      `(nil . ,*forwarding-symbol*)
      `(nil . ,object)))

(defmethod inform ((object basic-object)
                   (transformer-name (eql 'expand))
                   (whatami (eql 'lead)))
  t)

(defmethod pass ((object basic-object)
                 (trasformer-name (eql 'expand))
                 (args list-object))
  (declare (special *forwarding-symbol*))
  (if *forwarding-symbol*
      `(nil . ,(tcons *forwarding-symbol* args))
      `(nil . ,(tcons object args))))


;;;;;;;;;; symbol object ;;;;;;;;;;

(defmethod inform ((object symbol-object)
                   (transformer-name (eql 'expand))
                   (whatami (eql 'arg)))
  (declare (special *ctx* *forwarding-symbol*))
  (when *forwarding-symbol*
    (return-from inform `(nil . ,*forwarding-symbol*)))
  (let ((binding (maru-lookup *ctx* object)))
    (if binding
        (let ((*forwarding-symbol* object))
          (declare (special *forwarding-symbol*))
          (inform binding 'expand 'arg))
        `(nil . ,object))))

(defmethod inform ((object symbol-object)
                   (transformer-name (eql 'expand))
                   (whatami (eql 'lead)))
  (declare (special *ctx* *forwarding-symbol*))
  (when *forwarding-symbol*
    (return-from inform t))
  (let ((binding (maru-lookup *ctx* object)))
    (if binding
        (let ((*forwarding-symbol* object))
          (declare (special *forwarding-symbol*))
          (inform binding 'expand 'lead))
        t)))

;;; OF-NOTE: forwarding
(defmethod pass ((object symbol-object)
                 (transformer-name (eql 'expand))
                 (args list-object))
  (declare (special *ctx* *forwarding-symbol*))
  (when *forwarding-symbol*
    (return-from pass `(nil . ,(tcons *forwarding-symbol* args))))
  (let ((binding (maru-lookup *ctx* object)))
    (if binding
        (let ((*forwarding-symbol* object))
          (declare (special *forwarding-symbol*))
          (pass binding 'expand args))  ; must forward to actual form
        `(nil . ,(tcons object args)))))


;;;;;;;;;; form object ;;;;;;;;;;

(defmethod inform ((object form-object)
                   (transformer-name (eql 'expand))
                   (whatami (eql 'arg)))
  `(nil . ,object))

(defmethod inform ((object form-object)
                   (transformer-name (eql 'expand))
                   (whatami (eql 'lead)))
  nil)

(defmethod pass ((object form-object)
                 (transformer-name (eql 'expand))
                 (args list-object))
  (declare (special *ctx*))
  (let ((fn (function-object-fn object)))
    (typecase fn
      (runtime-closure-object (pass fn 'eval args))
      (function `(nil . ,(tapply-with-context fn *ctx* args))))))

;;;;;;;;;; list as lead ;;;;;;;;;;

(defmethod inform ((pair pair-object)
                   (transformer-name (eql 'expand))
                   (whatami (eql 'arg)))
  (declare (special *forwarding-symbol*))
  (if *forwarding-symbol*
      `(nil . ,*forwarding-symbol*)
      `(nil . ,pair)))

;; FIXME: do the right thing
(defmethod inform ((list pair-object)
                   (transformer-name (eql 'expand))
                   (whatami (eql 'lead)))
  t)

;; FIXME: do the right thing
(defmethod pass ((list pair-object)
                 (transformer-name (eql 'expand))
                 (args list-object))
  (declare (special *ctx*))
  (cons nil (tcons list args)))


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

(deftest test-tsugar
  (let-sugar (std-tfuncs)
    (and (equal '(1 . 2) (tcons 1 2))
         (eql 5 (tcar (tcons 5 4))))))

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

(deftest test-tokenize-parenlist-empty-list-bug
  (let ((next-char-fn (next-char-factory "(tokenize () this)")))
    (equal (tokenize next-char-fn)
           '("tokenize" nil "this"))))

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
    ;; consume the comma
    (funcall next-char-fn)
    (equal (unquote-handler next-char-fn nil)
           '("unquote" "something"))))

(deftest test-quote-handler
  (let ((next-char-fn
          (next-char-factory "'this")))
    ;; consume the quote
    (funcall next-char-fn)
    (equal (quote-handler next-char-fn nil)
           '("quote" "this"))))

(deftest test-desugar
  (let ((next-char-fn
          (next-char-factory "(this ,@(is text) ,so is ,,this)"))
        (read-table '((#\, . unquote-handler))))
    (equal (tokenize next-char-fn read-table)
           '("this" ("unquote-splicing" ("is" "text")) ("unquote" "so")
             "is" ("unquote" ("unquote" "this"))))))

(deftest test-desugar-quote
  (let ((next-char-fn
          (next-char-factory "(123 ''and '(a b c))"))
        (read-table '((#\' . quote-handler))))
    (equal (tokenize next-char-fn read-table)
           '("123" ("quote" ("quote" "and"))
                   ("quote" ("a" "b" "c"))))))

(deftest test-desugar-quasiquote
  (let ((next-char-fn
          (next-char-factory "(842 `(this that another (9)) `4)"))
        (read-table '((#\` . quasiquote-handler))))
    (equal (tokenize next-char-fn read-table)
           '("842" ("quasiquote" ("this" "that" "another" ("9")))
             ("quasiquote" "4")))))

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
        (typed-expr (mk-list (mk-symbol "some-fn")
                             (mk-symbol "a-sym")
                             (mk-list (mk-symbol "more")
                                      (mk-symbol "here"))
                             (mk-symbol "sym9001")))
        (ctx (maru-mk-ctx)))
    (eq-object typed-expr
               (transform type-transformer untyped-expr ctx))))

(deftest test-type-transformer-number
  (let ((type-transformer (make-transformer :name 'type))
        (untyped-expr (untype-everything
                        (tokenize
                          (next-char-factory
                            "(trees 0x123 (green 2) 0X456)"))))
        (typed-expr (mk-list (mk-symbol "trees") (mk-number "123" :hex t)
                             (mk-list (mk-symbol "green") (mk-number "2"))
                             (mk-number "456" :hex t)))
        (ctx (maru-mk-ctx)))
    (eq-object (transform type-transformer untyped-expr ctx) typed-expr)))

(deftest test-type-transform-char-and-string
  (let ((type-transformer (make-transformer :name 'type))
        (untyped-expr (untype-everything
                        (tokenize
                          (next-char-factory
                            "(running \"man\" ?r (u ?n \"s\") ?!)"))))
        (typed-expr
          (mk-list (mk-symbol "running")
                   (mk-string :value "man")
                   (mk-char #\r)
                   (mk-list (mk-symbol "u")
                            (mk-char #\n)
                            (mk-string :value "s"))
                   (mk-char #\!)))
        (ctx (maru-mk-ctx)))
    (eq-object (transform type-transformer untyped-expr ctx) typed-expr)))

(deftest test-type-quoted-list
  (let ((ctx (maru-initialize))
        (src "(define a '(1 (2 3)))")
        (typed-expr
          (mk-list (mk-symbol "define") (mk-symbol "a")
                   (mk-list (mk-symbol "quote")
                            (mk-list
                              (mk-number "1")
                              (mk-list (mk-number "2")
                                       (mk-number "3")))))))
    (eq-object typed-expr (type-expr ctx src))))

(deftest test-maru-intern
  (let* ((ctx (maru-mk-ctx))
         (out-sym (mk-symbol "hello-world"))
         (test-sym nil))
    (setf test-sym (maru-intern ctx "hello-world"))
    (and (eq-object test-sym out-sym)
         (member out-sym (maru-context-symbols ctx) :test 'eq-object)
         ;; dummy symbol
         (= 2 (length (maru-context-symbols ctx)))
         ;; dummy binding
         (= 1 (length (maru-env-bindings (maru-context-env ctx)))))))

(deftest test-intern-symbols-when-typing
  (let ((type-transformer (make-transformer :name 'type))
        (untyped-expr (untype-everything
                        (tokenize
                          (next-char-factory
                            "(type these (symbols 123) \"please\" kk)"))))
        (ctx (maru-mk-ctx))
        (out nil))
    (setf out (transform type-transformer untyped-expr ctx))
         ;; dummy binding
    (and (= 1 (length (maru-env-bindings (maru-context-env ctx))))
         (null (maru-env-parent (maru-context-env ctx)))
         ;; dummy symbol
         (= 5 (length (maru-context-symbols ctx)))
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
         ;; dummy symbol
         (= 2 (length (maru-context-symbols ctx)))
         ;; dummy binding
         (= 2 (length (maru-env-bindings (maru-context-env ctx)))))))

(deftest test-maru-lookup
  (let* ((ctx (maru-mk-ctx :parent-ctx (maru-mk-ctx)))
         (obj (mk-number "43"))
         (sym "some-symbol")
         (obj2 (mk-string :value "thisandthat"))
         (sym2 "another-symbol")
         (obj3 (mk-string :value "ballll"))
         (sym3 "in")
         (s3 nil)
         (doesntexist (maru-intern ctx "blahblah")))
    ;; global scope
    (maru-define ctx (maru-intern ctx sym) obj)
    ;; global scope
    (maru-define ctx (maru-intern ctx sym2) obj2)

    (setf s3 (maru-intern ctx sym3))
    ;; global scope
    (maru-define (maru-parent-ctx ctx) s3 obj3)

    (and (eq-object obj (maru-lookup ctx (mk-symbol sym)))
         (eq-object obj (maru-lookup (maru-parent-ctx ctx)
                                     (mk-symbol sym)))
         (eq-object obj2 (maru-lookup ctx (mk-symbol sym2)))
         (eq-object obj2 (maru-lookup (maru-parent-ctx ctx)
                                      (mk-symbol sym2)))
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
  (let-sugar (maru-tfuncs)
    (let* ((ctx (maru-initialize))
           (a (mk-string :value "this"))
           (b (mk-number "200"))
           (out nil))
      (setf out
            (funcall (function-object-fn
                       (maru-lookup ctx (maru-intern ctx "cons")))
                     ctx (mk-list a b)))
      (and (eq-object a (maru-car out))
           (eq-object b (maru-cdr out))))))

(deftest test-maru-eval-transform-simple
  (let* ((ctx (maru-initialize))
         (eval-transformer (make-transformer :name 'eval))
         (untyped-expr (untype-everything
                         (tokenize
                           (next-char-factory "(cons \"kewl\" 22)"))))
         (type-transformer (make-transformer :name 'type))
         (typed-expr (transform type-transformer untyped-expr ctx))
         (out nil))
    (setf out (transform eval-transformer
                         typed-expr
                         ctx
                         :tfuncs (maru-tfuncs)))
    (eq-object (mk-pair (mk-string :value "kewl") (mk-number "22"))
               out)))

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
    (maru-define ctx (mk-symbol "kewl") (mk-string :value "astronauts"))
    (setf out (transform eval-transformer
                         typed-expr
                         ctx
                         :tfuncs (maru-tfuncs)))
    (and (eq-object (maru-car out)  (mk-string :value "astronauts"))
         (eq-object (maru-car (maru-cdr out)) (mk-number "100"))
         (eq-object (maru-cdr (maru-cdr out)) (mk-number "22")))))

(deftest test-maru-primitive-if-simple
  (let ((ctx (maru-initialize)))
         ;; test 'then' branch
    (and (eq-object (mk-string :value "goodbye")
                    (funcall (function-object-fn
                               (maru-lookup ctx (mk-symbol "if")))
                             ctx
                             (mk-list
                               (mk-string :value "not-nil")  ;; predicate
                               (mk-string :value "goodbye")  ;; then
                               (mk-number "100"))))          ;; else
         ;; test 'else' branch
         (eq-object (mk-number "14")
                    (funcall (function-object-fn
                                (maru-lookup ctx (maru-intern ctx "if")))
                             ctx
                             (mk-list
                               (maru-nil)                 ;; predicate
                               (mk-number "12")           ;; then
                               (mk-number "14")))))))      ;; else

(defun untype-expr (src)
  (let ((read-table '((#\' . quote-handler) (#\, . unquote-handler)
                      (#\` . quasiquote-handler))))
    (untype-everything
      (tokenize (next-char-factory src) read-table))))

(defun type-expr (ctx src)
  (transform (make-transformer :name 'type) (untype-expr src) ctx))

(defun maru-all-transforms (ctx src)
  (let ((expand-transformer (make-transformer :name 'expand))
        (eval-transformer (make-transformer :name 'eval))
        (typed-expr (type-expr ctx src))
        (expanded-expr nil)
        (evald-expr nil))
    ; (when (atom typed-expr)
        ; (format t "TYPED: ~A~%" (maru-printable-object typed-expr)))
    (setf expanded-expr
          (transform expand-transformer
                     typed-expr
                     ctx
                     :tfuncs (maru-tfuncs)))
    ; (when (atom expanded-expr)
        ; (format t "EXPAND: ~A~%" (maru-printable-object expanded-expr)))
    (setf evald-expr
          (transform eval-transformer
                     expanded-expr
                     ctx
                     :tfuncs (maru-tfuncs)))
    ; (when (atom evald-expr)
        ; (format t "EVALD : ~A~%" (maru-printable-object evald-expr)))
    evald-expr))


(deftest test-maru-eval-with-fixed
  (let* ((ctx (maru-initialize))
         (eval-transformer (make-transformer :name 'eval))
         (typed-expr (type-expr ctx "(if 100 200 300)")))
    (eq-object (mk-number "200")
               (transform eval-transformer
                          typed-expr
                          ctx
                          :tfuncs (maru-tfuncs)))))

(deftest test-maru-primitive-and
  (let ((ctx (maru-initialize)))
    (declare (special *ctx* *tfuncs*))
    (setf *ctx* ctx)
    ; (setf *tfuncs* (maru-tfuncs))
    ;; FIXME: why does this require std-tfuncs?
    (setf *tfuncs* (std-tfuncs))
    (and (eq-object (mk-string :value "last")
                    (funcall (function-object-fn
                               (maru-lookup ctx (mk-symbol "and")))
                             ctx
                             (mk-list
                               (mk-string :value "first")
                               (mk-string :value "second")
                               (mk-string :value "last"))))
         (maru-nil? (funcall (function-object-fn
                               (maru-lookup ctx (mk-symbol "and")))
                             ctx
                             (mk-list
                               (mk-string :value "first")
                               (mk-string :value "second")
                               (mk-string :value "third")
                               (maru-nil)))))))

(deftest test-maru-eval-with-form
  (let* ((ctx (maru-initialize))
         (expand-transformer (make-transformer :name 'eval))
         (typed-expr (type-expr ctx "(and 1 2 3 20)")))
    (eq-object (mk-number "20")
               (transform expand-transformer
                          typed-expr
                          ctx
                          :tfuncs (maru-tfuncs)))))

(deftest test-maru-simple-expand-and-eval
  (let* ((ctx (maru-initialize))
         (evaled-expr
           (maru-all-transforms ctx
                                "(cons (and 1 3 \"hello\") \"world\")")))
    (and (eq-object (maru-car evaled-expr) (mk-string :value "hello"))
         (eq-object (maru-cdr evaled-expr) (mk-string :value "world")))))

;; no longer an expand bug as define is no longer a macro
(deftest test-maru-expand-bug
  (let* ((ctx (maru-initialize))
         (evaled-expr
           (maru-all-transforms ctx
                                "(cons (define a 3) 4)")))
    (and (eq-object evaled-expr (mk-pair (mk-number "3")
                                         (mk-number "4"))))))

;; no longer an expand bug as define is no longer a macro
(deftest test-maru-expand-bug-2
  "macros in the lambda body should be expanded"
  (let* ((ctx (maru-initialize))
         (evaled-expr
           (maru-all-transforms ctx
                                "(block
                                   (define fn (lambda (a) (define a 3)))
                                   (fn 5))")))
    (and (eq-object (mk-number "3") evaled-expr))))

(deftest test-maru-primitive-define
  (let* ((ctx (maru-initialize))
         (expand-transformer (make-transformer :name 'eval))
         (typed-expr (type-expr ctx "(define a \"some-value\")"))
         (def-sym (mk-symbol "define"))
         (a-sym (mk-symbol "a"))
         (expanded-expr (transform expand-transformer
                                   typed-expr
                                   ctx
                                   :tfuncs (maru-tfuncs))))
    (declare (ignore expanded-expr))
         ; did we add 'define' successfully?
    (and (member def-sym (maru-context-symbols ctx) :test #'eq-object)
         ; did we add 'a' successfully with define?
         (member a-sym (maru-context-symbols ctx) :test #'eq-object)
         (eq-object (mk-string :value "some-value")
                    (maru-lookup ctx a-sym)))))

(deftest test-maru-redefine-bug
  (let* ((ctx (maru-initialize))
         (src "(block
                 (define a 10)
                 (let ()
                   (define a 20))
                 a)"))
    (eq-object (mk-number "20")
               (maru-all-transforms ctx src))))

(deftest test-maru-primitive-arithmetic
  (let* ((ctx (maru-initialize))
         (src "(- (/ (* 5 (+ 8 4)) 2) 9)")
         (result (maru-all-transforms ctx src)))
    (and (binding-exists? ctx "-") (binding-exists? ctx "+")
         (binding-exists? ctx "*") (binding-exists? ctx "/")
         (eq-object result (mk-number "21")))))

(deftest test-maru-primitive-ordering
  (let* ((ctx (maru-initialize))
         (src "(block
                 (define a 4)
                 (cons (< a 5)
                       (cons (> a 4)
                             (cons (= a \"this\")
                                   (cons (>= a 4)
                                         (cons (<= a 4)
                                               (!= a 55)))))))"))
    (eq-object (mk-pair (mk-bool t)
                        (mk-pair (mk-bool nil)
                                 (mk-pair (mk-bool nil)
                                          (mk-pair (mk-bool t)
                                                   (mk-pair
                                                     (mk-bool t)
                                                     (mk-bool t))))))
               (maru-all-transforms ctx src))))

(deftest test-maru-primitive-lambda
  (let* ((ctx (maru-initialize))
         (src "(define fn (lambda (a b) (* a (+ 2 b))))")
         (lambda-sym (mk-symbol "lambda"))
         (result (maru-all-transforms ctx src)))
    (declare (ignore result))
         ; did we add 'lambda' successfully
    (and (member lambda-sym (maru-context-symbols ctx) :test #'eq-object)
         ; does the lambda compute the value?
         (eq-object (mk-number "40")
                    (maru-all-transforms ctx "(fn 2 (fn 3 4))")))))

(deftest test-maru-pass-scalar-to-lambda
  (let* ((ctx (maru-initialize))
         (src0 "(define a 100)")
         (src1 "(define fn (lambda (x) (+ 200 x)))"))
    (maru-all-transforms ctx src0)
    (maru-all-transforms ctx src1)
    (eq-object (mk-number "300")
               (maru-all-transforms ctx "(fn a)"))))

(deftest test-maru-pass-cons-to-lambda
  (let* ((ctx (maru-initialize))
         (src0 "(define k (cons 1 (cons 2 3)))")
         (src1 "(define fn (lambda (l) (car (cdr l))))"))
    (maru-all-transforms ctx src0)
    (maru-all-transforms ctx src1)
    (eq-object (mk-number "2")
               (maru-all-transforms ctx "(fn k)"))))

(deftest test-maru-lambda-no-mutate-scalar
  "lambdas should not mutate scalar values in an outer env"
  (let* ((ctx (maru-initialize))
         (src0 "(block
                  (define s 30)
                  (define fn (lambda (j)
                               (set j 45)
                               (cons s j)))
                  (fn s))")
         (ess "(block s)"))
    (and (eq-object (mk-pair (mk-number "30") (mk-number "45"))
                    (maru-all-transforms ctx src0))
         (eq-object (mk-number "30")
                    (maru-all-transforms ctx ess)))))

(deftest test-maru-lambda-mutate-cons-cell
  "lambdas should be able to mutate cons cells from an outer env"
  (let* ((ctx (maru-initialize))
         (src0 "(define c (cons 1001 2002))")
         (src1 "(define mutate (lambda (e) (set-car e 5005)))")
         (src2 "(mutate c)")
         (cee "(cons (car c) (cdr c))"))    ; hack to get value of c
    (maru-all-transforms ctx src0)
    (maru-all-transforms ctx src1)
    (and (eq-object (mk-number "5005")
                    (maru-all-transforms ctx src2))
         (eq-object (mk-pair (mk-number "5005") (mk-number "2002"))
                    (maru-all-transforms ctx cee)))))

(deftest test-maru-primitive-block
  (let* ((ctx (maru-initialize))
         (src0 "(block
                  (define a (cons 1 2))
                  (set-car a 15)
                  100)")
         (a "(cons (car a) (cdr a))"))
    (and (eq-object (mk-number "100")
                    (maru-all-transforms ctx src0))
         (eq-object (mk-pair (mk-number "15") (mk-number "2"))
                    (maru-all-transforms ctx a))
         ;; empty block should return nil
         (eq-object (maru-all-transforms ctx "(block)")
                    (maru-nil)))))

(deftest test-lambda-implicit-block
  "lambdas have implicit blocks"
  (let* ((ctx (maru-initialize))
         (src0 "(block
                  (define g (cons 12 13))
                  (define fn (lambda (a)
                                (set-car a 20)
                                250
                                300))
                  (fn g))")
         (gee "(cons (car g) (cdr g))"))
    (and (eq-object (mk-number "300")
                    (maru-all-transforms ctx src0))
         (eq-object (mk-pair (mk-number "20") (mk-number "13"))
                    (maru-all-transforms ctx gee)))))

(deftest test-applicator-from-internal
  "should be able to take an applicator and get it's internal function"
  nil)

(deftest test-binding-precedence
  (let* ((ctx (maru-initialize))
         (src0 "(block
                  (define a (cons 1 3))
                  (define fn (lambda (a)
                               (define a 20)
                               a))
                  (fn a))")
         (a "(block a)"))
    ;; the define inside of the lambda only affects things outside of
    ;; the lambda because define works at global scope
    (and (eq-object (mk-pair (mk-number "1") (mk-number "3"))
                    (maru-all-transforms ctx src0))
         (eq-object (mk-number "20")
                    (maru-all-transforms ctx a)))))

(deftest test-binding-precedence-2
  (let* ((ctx (maru-initialize))
         (src0 "(block
                  (define a (cons 1 3))
                  (define fn (lambda (a)
                               (set-car a 550)
                               a))
                  (fn a))")
         (a "(block a)"))
    (and (eq-object (mk-pair (mk-number "550") (mk-number "3"))
                    (maru-all-transforms ctx src0))
         (eq-object (mk-pair (mk-number "550") (mk-number "3"))
                    (maru-all-transforms ctx a)))))

(deftest test-let-create-new-bindings-bug
  "let and lambda should always create new bindings"
  (let* ((ctx (maru-initialize))
         (src "(block
                 (define a 30)
                 (let ((a 15))
                   100)
                 a)"))
    (eq-object (mk-number "30")
               (maru-all-transforms ctx src))))

(deftest test-maru-spawn-child-env
  (let ((ctx (maru-initialize))
        (child-ctx nil))
    (maru-intern ctx "this")
    ;; global
    (maru-define ctx (maru-intern ctx "that") (mk-number "15"))
    (setf child-ctx (maru-spawn-child-env ctx))
    (maru-intern child-ctx "or")
    ;; global
    (maru-define child-ctx (maru-intern child-ctx "theother")
                           (mk-number "16"))
         ;; added stuff to parent env?
    (and (not (binding-exists? ctx "this"))
         (member (mk-symbol "this") (maru-context-symbols ctx)
                 :test #'eq-object)
         (binding-exists? ctx "that")
         (not (binding-exists? ctx "or"))
         (binding-exists? ctx "theother")
         ; child symbols still valid
         (member (mk-symbol "or") (maru-context-symbols ctx)
                 :test #'eq-object)
         (member (mk-symbol "theother") (maru-context-symbols ctx)
                 :test #'eq-object)
         ;; added stuff to child env
         (not (binding-exists? child-ctx "or"))
         (member (mk-symbol "or") (maru-context-symbols child-ctx)
                 :test #'eq-object)
         (binding-exists? child-ctx "theother")
         ;; can still get stuff from parent env
         (not (binding-exists? child-ctx "this"))
         (member (mk-symbol "this") (maru-context-symbols child-ctx)
                 :test #'eq-object)
         (binding-exists? child-ctx "that"))))

(deftest test-maru-nil
       ;; empty list is equivalent to nil
  (and (eq-object (maru-nil) (maru-nil))
       (eq-object (mk-list) (maru-nil))
       (eq-object (maru-nil) (mk-list))
       (eq-object (mk-list) (mk-list))
       ;; a pair with two nils is not nil
       (not (eq-object (mk-pair (maru-nil) (maru-nil))
                       (maru-nil)))
       (not (eq-object (maru-nil)
                       (mk-pair (maru-nil) (maru-nil))))
       ;; a pair with two nils is a list with a single nil
       (eq-object (mk-pair (maru-nil) (maru-nil))
                  (mk-list (maru-nil)))
       (eq-object (mk-list (maru-nil))
                  (mk-pair (maru-nil) (maru-nil)))
       ;; a list with a single nil is not nil
       (not (eq-object (mk-list (maru-nil))
                       (maru-nil)))
       (not (eq-object (maru-nil)
                       (mk-list (maru-nil))))
       ;; a cons with a cdr nil is a list
       (eq-object (mk-list (mk-string :value "yes"))
                  (mk-pair (mk-string :value "yes") (maru-nil)))
       (eq-object (mk-pair (mk-string :value "yes") (maru-nil))
                  (mk-list (mk-string :value "yes")))))

(deftest test-maru-list
  (let ((list-object (mk-list (mk-number "1") (mk-string :value "yes")
                              (mk-string :value "goat"))))
    (and (eq-object (mk-number "1") (maru-car list-object))
         (eq-object (mk-string :value "yes")
                    (maru-car (maru-cdr list-object)))
         (eq-object (mk-list (mk-string :value "yes")
                             (mk-string :value "goat"))
                    (maru-cdr list-object)))))

(deftest test-maru-pair-primitives
  (let-sugar (maru-tfuncs)
  (let* ((ctx (maru-initialize))
         (pair (funcall (function-object-fn
                          (maru-lookup ctx (mk-symbol "cons")))
                        ctx
                        (mk-list
                          (mk-string :value "uno")
                          (mk-list
                            (mk-string :value "dos")
                            (mk-string :value "tres")))))
         (test (mk-list
                 (mk-string :value "uno")
                 (mk-string :value "dos")
                 (mk-string :value "tres"))))
    (and (eq-object pair test)
         (eq-object (funcall (function-object-fn
                               (maru-lookup ctx (mk-symbol "car")))
                               ctx
                               (mk-list test))
                    (maru-car test))
         (eq-object (funcall (function-object-fn
                               (maru-lookup ctx (mk-symbol "cdr")))
                               ctx
                               (mk-list test))
                    (maru-cdr test))))))

(deftest test-maru-mutating-pair-primitives
  (let* ((ctx (maru-initialize))
         (list (mk-pair (mk-string :value "cyber")
                        (mk-pair (mk-string :value "space")
                                 (mk-pair (mk-number "12")
                                          (mk-number "15")))))
         (src0 "(define list (cons \"cyber\" (cons \"space\"
                                                   (cons 12 15))))")
         (src1 "(set-car list 100)")
         (src2 "(set-cdr list 250)")
         (car-list "(car list)")
         (cdr-list "(cdr list)"))
    (maru-all-transforms ctx src0)
    ; does car mutation work?
    (maru-all-transforms ctx src1)
    (and (eq-object (mk-number "100")
                    (maru-all-transforms ctx car-list))
         (eq-object (maru-cdr list)
                    (maru-all-transforms ctx cdr-list))
         ; does cdr mutation work
         (progn
           (maru-all-transforms ctx src2)
           t)
         (eq-object (mk-number "100")
                    (maru-all-transforms ctx car-list))
         (eq-object (mk-number "250")
                    (maru-all-transforms ctx cdr-list)))))

(deftest test-maru-macro-symbol-eval-bug
  ~"this bug is hard to test for; other than to say that this should run;"
  ~" the problem was the expand was evaluating symbols are were already"
  " binded to non-macros"
  (let* ((ctx (maru-initialize))
         (src0 "(block
                  (define tt 10)
                  (define ff (lambda (tt) 5))
                  (ff 12))"))
    (eq-object (mk-number "5") (maru-all-transforms ctx src0))))

(deftest test-maru-set-macro-primitive
  (let* ((ctx (maru-initialize))
         (src0 "(block
                  (define set-something (lambda (x y) (+ x y)))
                  (set (something 15) 20))"))
    (eq-object (mk-number "35")
               (maru-all-transforms ctx src0))))

(deftest test-maru-set-runtime-primitive
  (let* ((ctx (maru-initialize))
         (src0 "(block
                  (define yesterday 55)
                  (set yesterday 34)
                  yesterday)"))
    (eq-object (mk-number "34")
               (maru-all-transforms ctx src0))))

(deftest test-maru-let-primitive
  (let* ((ctx (maru-initialize))
         (src0 "(block
                  (define fn (lambda (a b)
                               (let ((a 20)
                                     (c 30))
                                 (+ (+ a b) c))))
                  (fn 5 7))"))
    (eq-object (mk-number "57")
               (maru-all-transforms ctx src0))))

(deftest test-maru-let-primitive-bug
  "values in let bindings must be evaluated"
  (let* ((ctx (maru-initialize))
         (src "(let ((a '()))
                 a)"))
    (eq-object (maru-nil)
               (maru-all-transforms ctx src))))

(deftest test-maru-let-primitive-implicit-binding-block-bug
  "values in let bindings are in implicit block"
  (let* ((ctx (maru-initialize))
         (src "(block
                 (define a 20)
                 (let ((b (define a 250) 5 6))
                   b))")
         (a "(block a)"))
    (and (eq-object (mk-number "6")
                    (maru-all-transforms ctx src))
         (eq-object (mk-number "250")
                    (maru-all-transforms ctx a)))))

(deftest test-maru-empty-list-bug
  (let* ((ctx (maru-initialize))
         (src "(let ()
                 7)"))
    (maru-all-transforms ctx src)))

(deftest test-maru-while-primitive
  (let* ((ctx (maru-initialize))
         (src0 "(block
                  (define i 0)
                  (define out (cons 10 10))
                  (while (< i 3)
                    (set out (cons i out))
                    (set i (+ i 1)))
                  out)"))
    (eq-object (mk-pair (mk-number "2")
                        (mk-pair (mk-number "1")
                                 (mk-pair (mk-number "0")
                                          (mk-pair (mk-number "10")
                                                   (mk-number "10")))))
               (maru-all-transforms ctx src0))))

(deftest test-maru-pair?-primitive
  (let* ((ctx (maru-initialize))
         (src0 "(block
                  (define n 10)
                  (define p (cons 1 2))
                  (cons (pair? n) (pair? p)))"))
    (eq-object (mk-pair (mk-bool nil) (mk-bool t))
               (maru-all-transforms ctx src0))))

(deftest test-maru-pair?-primitive-bug
  (let* ((ctx (maru-initialize))
         (src "(pair? '())"))
    (eq-object (maru-nil)
               (maru-all-transforms ctx src))))

(deftest test-maru-assq
  (let ((ctx (maru-initialize))
        (code "(define assq
                 (lambda (object lst)
                   (let ((result '()))
                     (while (pair? lst)
                       (if (= object (caar lst))
                           (let ()
                             (set result (car lst))
                             (set lst '()))
                           (set lst (cdr lst))))
                     result)))")
        (use-it "(block
                   (define alist '((3 33) (4 44) (5 55)))
                   (cons (assq 4 alist) (assq \"12\" alist)))"))
    (maru-all-transforms ctx code)
    (eq-object (mk-pair (mk-list (mk-number "4")
                                 (mk-number "44"))
                        (maru-nil))
               (maru-all-transforms ctx use-it))))

(deftest test-maru-concat-string
  (let ((ctx (maru-initialize))
        (code "(define concat-string
                 (lambda (x y)
                   (let ((a (string-length x))
                     (b (string-length y)))
                     (let ((s (string (+ a b)))
                       (i 0)
                       (j 0))
                   (while (< i a)
                     (set-string-at s j (string-at x i))
                     (set i (+ i 1))
                     (set j (+ j 1)))
                   (set i 0)
                   (while (< i b)
                     (set-string-at s j (string-at y i))
                     (set i (+ i 1))
                     (set j (+ j 1)))
                   s))))")
        (use-it "(block
                   (define s0 \"abc\")
                   (define s1 \"xyz\")
                   (= \"abcxyz\"
                      (concat-string s0 s1)))"))
    (maru-all-transforms ctx code)
    (not (eq-object (maru-nil)
                    (maru-all-transforms ctx use-it)))))

(deftest test-maru-string-primitive
  (let ((ctx (maru-initialize))
        (code "(string 20)"))
    (eq-object (mk-string :size 20)
               (maru-all-transforms ctx code))))

(deftest test-maru-string-length-primitive
  (let ((ctx (maru-initialize))
        (code "(string-length (string 55))"))
    (eq-object (mk-number "55")
               (maru-all-transforms ctx code))))

(deftest test-maru-string-at-primitive
  (let ((ctx (maru-initialize))
        (code "(cons (string-at \"yessir-nosir\" 2)
                     (string-at \"short\" 100))"))
    (eq-object (mk-pair (mk-char #\s) (maru-nil))
               (maru-all-transforms ctx code))))

(deftest test-maru-set-string-at-primitive
  (let ((ctx (maru-initialize))
        (code "(block
                 (define s \"anything-goes\")
                 (cons (set-string-at s 1 ?r)
                       (set-string-at s 100 ?j)))"))
    (eq-object (mk-pair (mk-string :value "arything-goes") (maru-nil))
               (maru-all-transforms ctx code))))

(deftest test-maru-list-primitive
  (let ((ctx (maru-initialize))
        (src "(list 1 2 (list \"three\" (list 4)) \"five\")"))
    (eq-object (mk-list (mk-number "1") (mk-number "2")
                        (mk-list (mk-string :value "three")
                                 (mk-list (mk-number "4")))
                        (mk-string :value "five"))
               (maru-all-transforms ctx src))))

(deftest test-maru-define-form
  (let ((ctx (maru-initialize))
        (src "(block
                (define define-form (form (lambda (name args . body)
                  `(define ,name (form (lambda ,args ,@body))))))
                (define-form define-function (name args . body)
                  `(define ,name (lambda ,args ,@body)))
                (define-function list-length (list)
                  (if (pair? list)
                      (+ 1 (list-length (cdr list)))
                      0))")
        (use-it "(cons (list-length '()) (list-length (0 1 2 3)))"))
    (declare (ignore ctx src use-it))
    nil))
#|
    (maru-all-transforms ctx src)
    (eq-object (mk-pair (maru-nil) (mk-number 4))
               (maru-all-transforms ctx use-it))))
|#

(deftest test-maru-map
  (let ((ctx (maru-initialize))
        (src "(define-function map (function list)
                (if (pair? list)
                    (let ((head (function (car list))))
                  (cons head (map function (cdr list))))))"))
    (declare (ignore ctx src))
    nil))

;; FIXME: this seems to be close; but not quite right, hard to test
(deftest test-maru-quasiquote
  (let ((ctx (maru-initialize))
        (src "(define quasiquote
                (form
                  (let ((qq-list) (qq-element) (qq-object))
                    (set qq-list (lambda (l)
                                   (if (pair? l)
                                     (let ((obj (car l)))
                                       (if (and (pair? obj)
                                                (= (car obj)
                                                   'unquote-splicing))
                                           (if (cdr l)
                                               (list 'concat-list
                                                     (cadr obj)
                                                     (qq-list (cdr l)))
                                               (cadr obj))
                                           (list 'cons
                                                 (qq-object obj)
                                                 (qq-list (cdr l)))))
                                     (list 'quote l))))
                    (set qq-element (lambda (l)
                                      (let ((head (car l)))
                                        (if (= head 'unquote)
                                            (cadr l)
                                            (qq-list l)))))
                    (set qq-object (lambda (object)
                                     (if (pair? object)
                                         (qq-element object)
                                         (list 'quote object))))
                    (lambda (expr)
                      (qq-object expr)))))")
        (use-it-0 "`(1 (2) 3)")
        (use-it-1 "`9"))
    (maru-all-transforms ctx src)
    (and (eq-object (mk-list (mk-number "1")
                             (mk-list (mk-number "2"))
                             (mk-number "3"))
                    (maru-all-transforms ctx use-it-0))
         (eq-object (mk-number "9")
                    (maru-all-transforms ctx use-it-1)))))

(deftest test-maru-closure-context
  (let ((ctx (maru-initialize))
        (src "(define fn
                (let ((c 2))
                  (lambda (d)
                    (+ c d))))")
        (use-it "(fn 5)"))
    (maru-all-transforms ctx src)
    (eq-object (mk-number "7")
               (maru-all-transforms ctx use-it))))

(deftest test-maru-global-counter
  (let ((ctx (maru-initialize))
        (src "(block
                (define n 0)
                (define inc (lambda () (set n (+ 1 n))))
                (define reset (lambda () (set n 0)))
                (define get (lambda () n)))")
        (use-it-0 "(block
                     (inc) (inc) (reset) (inc) (get))")
        (use-it-1 "(block
                     (inc) (reset) (reset) (reset))"))
    (maru-all-transforms ctx src)
    (and (eq-object (mk-number "1")
                    (maru-all-transforms ctx use-it-0))
         (eq-object (mk-number "0")
                    (maru-all-transforms ctx use-it-1)))))

(deftest test-maru-closure-counter
  (let ((ctx (maru-initialize))
        (src "(let ((n 0))
                (define inc (lambda () (set n (+ 1 n))))
                (define reset (lambda () (set n 0))))")
        (use-it-0 "(block
                     (inc) (inc) (inc))")
        (use-it-1 "(block
                     (reset) (inc) (reset) (inc) (inc))"))
    (maru-all-transforms ctx src)
    (and (eq-object (mk-number "3")
                    (maru-all-transforms ctx use-it-0))
         (eq-object (mk-number "2")
                    (maru-all-transforms ctx use-it-1)))))

(deftest test-maru-doesnt-require-quote-nil
  ~"because imaru reads itself into maru list type it doesn't need"
  ~" to quote the empty list, we should match this"
  (let ((ctx (maru-initialize))
        (src "(= () '())"))
    (eq-object (mk-bool t)
               (maru-all-transforms ctx src))))

(deftest test-define-scope
  (let ((ctx (maru-initialize))
        (src "(block
                (define fn
                  (lambda ()
                    (define a 10)))
                (fn)
                (define b 44))")
        (use-it "(block (cons a b))"))
    (maru-all-transforms ctx src)
    (eq-object (mk-pair (mk-number "10")
                        (mk-number "44"))
               (maru-all-transforms ctx use-it))))

(deftest test-quote-pairing@typing
  (let ((ctx (maru-initialize))
        (src0 "'(1 2 a)")
        (src1 "'5"))
    (and (eq-object (mk-list (mk-number "1")
                             (mk-number "2")
                             (mk-symbol "a"))
                     (maru-all-transforms ctx src0))
         (eq-object (mk-number "5")
                    (maru-all-transforms ctx src1)))))

(deftest test-macros
  (let ((ctx (maru-initialize))
        (src "(define m
                (form
                  (let ((fn) (gn))
                    (set fn
                      (lambda (n)
                        (* n 10)))
                    (set gn
                      (lambda (i)
                        (list 'cons i i)))
                    (lambda ()
                        (gn (fn 5))))))")
        (use-it "(m)"))
    (maru-all-transforms ctx src)
    (eq-object (mk-pair (mk-number "50") (mk-number "50"))
               (maru-all-transforms ctx use-it))))

(deftest test-list-conversion
  (let ((maru-list-0 (mk-list (mk-number "1") (mk-number "2")
                              (mk-list (mk-number "3") (mk-number "4"))
                              (mk-list (mk-number "5") (mk-number "6"))
                              (mk-number "7")))
        (maru-list (mk-list (mk-number "1")
                            (mk-number "2")
                            (mk-list (mk-number "9")
                                     (mk-number "0"))
                            (mk-list (mk-list (mk-number "2"))
                                     (mk-number "0")))))
    (and (eq-object (internal-list-to-maru-list
                      (maru-list-to-internal-list maru-list-0))
                    maru-list-0)
         (eq-object (internal-list-to-maru-list
                      (maru-list-to-internal-list maru-list))
                    maru-list))))

