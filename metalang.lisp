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
;;;; > array and list comparison can't use eq-object behind ``='' as the
;;;;   test needs to determine if they are the same object
;;;; > why do we need to duplicate the null terminator implementation
;;;;   for strings?
;;;; > fix the disparity between chars and numbers that doesn't exist in
;;;;   imaru (longs)
;;;; > abstract typecasing of function-object applications
;;;; > runtime-closure-object should be in the function-object hierarchy?
;;;; > mk-number take integer argument
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
;;;; . pseudoforms are currently a hack
;;;;   > ``set'' should happen after expansion and before evaluation; so
;;;;     it occurs in the 'pseudoexpand transformation
;;;;   > the semantics are exactly the same as the 'expand transformation
;;;;     except we want to deal with a seperate set of identifiers; the
;;;;     ``pseudoexpanders''
;;;;   > we can't make ``set'' a macro that we treat conditionally because
;;;;     expansion doesn't end until all macros are expanded; so we never
;;;;     make it out of vanilla expansion
;;;;   > we also want to avoid duplicating expand semantics into pexpand
;;;;     handlers; currently we use the *pseudoexpansion* identifier and
;;;;     the form-helper function, not totally clean

(proclaim '(optimize (debug 3)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;          Tokenizor
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-condition token-error (error)
  ((text :initarg :text)))

(defun whitespace? (c)
  (member c '(#\Backspace #\Tab #\Newline #\Linefeed #\Page #\Space)))

(defun paren? (c)
  (member c '(#\( #\))))

(defun tokenize-parenlist (next-char-fn read-table)
  (let ((c (funcall next-char-fn))
        (exprs '()))
    (assert (char= c #\())
    (do ((char (funcall next-char-fn 'peek) (funcall next-char-fn 'peek)))
        ((char= char #\)) exprs)
      (let ((e (tokenize next-char-fn read-table)))
        ; push empty lists but not empty strings (whitespace)
        (unless (and (typep e 'string) (zerop (length e)))
          (if (equal "." e)
              (progn
                ;; must have an expression before the dot
                (when (null exprs)
                  (error 'token-error :text "need expr before dot"))
                (setf exprs (reverse exprs))
                ;; read the expression after the dot
                (setf (cdr (last exprs))
                      (tokenize next-char-fn read-table))
                ;; expression after the dot is last
                (unless (char= #\) (funcall next-char-fn))
                  (error 'token-error :text "only one expr after dot"))
                (return-from tokenize-parenlist exprs))
              (push e exprs)))))
    (assert (char= #\) (funcall next-char-fn)))
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
    (cond ((null c) (error 'token-error :text "no form to tokenize"))
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

(defun doublequote-handler (next-char-fn read-table)
  (declare (ignore read-table))
  (let ((output ""))
    (do ((c (funcall next-char-fn) (funcall next-char-fn)))
        ((char-equal c #\") output)
      (when (char-equal #\\ c)
        (setf c (funcall next-char-fn)))
      (setf output (scat output c)))
    (scat "\"" output "\"")))

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

(defun maru-typer ()
  (make-transformer :name 'type))

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
  car cdr cons null nil atom listp proper?)

(declaim (special *tcar* *tcdr* *tcons* *tnull*
                  *tnil* *tatom* *tlistp* *tproper?*))

(defmacro let-sugar (tfuncs &rest body)
  `(let ((*tcar* (tfuncs-car ,tfuncs))   (*tcdr* (tfuncs-cdr ,tfuncs))
         (*tcons* (tfuncs-cons ,tfuncs)) (*tnull* (tfuncs-null ,tfuncs))
         (*tnil* (tfuncs-nil ,tfuncs))   (*tatom* (tfuncs-atom ,tfuncs))
         (*tlistp* (tfuncs-listp ,tfuncs))
         (*tproper?* (tfuncs-proper? ,tfuncs)))
     ,@body))

(defsugar tcar)
(defsugar tcdr)
(defsugar tcons)
(defsugar tnull)
(defsugar tnil)
(defsugar tatom)
(defsugar tlistp)
(defsugar tproper?)

(defun std-tfuncs ()
  (make-tfuncs :car   #'car
               :cdr   #'cdr
               :cons  #'cons
               :null  #'null
               :nil   #'(lambda () nil)
               :atom  #'atom
               :listp #'listp
               :proper? #'proper-<fails-on-circular>?))

(defun tlength (tlist)
  (cond ((tnull tlist) 0)
        (t (1+ (tlength (tcdr tlist))))))

(defun rude-tmapcar (fn tlist)
  (assert (tlistp tlist))
  (cond ((tnull tlist) (tnil))
        (t (tcons (funcall fn (tcar tlist))
                  (if (and (not (tnull (tcdr tlist)))
                           (tatom (tcdr tlist)))
                      (funcall fn (tcdr tlist))
                      (rude-tmapcar fn (tcdr tlist)))))))

(defun tmapcar (fn tlist)
  (assert (tlistp tlist))
  (cond ((tnull tlist) (tnil))
        (t (tcons (funcall fn (tcar tlist))
                  (tmapcar fn (tcdr tlist))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;    transformation
;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
  (assert (tproper? expr-args))
  ;; response : can-i-talk-to-your-arguments?
  (let* ((response (inform lead (transformer-name transformer) 'lead))
         (args (tmapcar
                 #'(lambda (a)
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
;;; > tfuncs may only be valid for the input data format
(defun transform (transformer expr ctx &key (tfuncs (std-tfuncs)))
  (let-sugar tfuncs
    (let ((*ctx* ctx)
          (*tfuncs* tfuncs))    ; necessary for recursive calls
      (declare (special *ctx* *tfuncs*))
      (cond ((tnull expr) (tnil))
            ((tatom expr)
             (back-talk-arg transformer expr))
            ((not (tproper? expr))
             (rude-tmapcar
               #'(lambda (a)
                   (back-talk-arg transformer a))
               expr))
            (t
              (back-talk-sexpr transformer
                               (tcar expr)
                               :expr-args (tcdr expr)))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;            maru
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-condition exit-program-signal (error)
  ((code :initarg :code)))

(define-condition bad-type-of (error)
  ())

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
  (:method ((object array-object))
    "<array-object>")
  (:method ((object pair-object))
    (scat "("
          (maru-printable-object (pair-object-car object))
          " . "
          (maru-printable-object (pair-object-cdr object))
          ")"))
  (:method ((object raw-object))
    (format nil "<raw-object :type => ~A, :size => ~A>"
                (raw-object-type object)
                (length (raw-object-mem object)))))

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

(defmethod maru-proper? ((pair list-object))
  (cond ((maru-nil? (maru-cdr pair)) t)
        ((maru-list? (maru-cdr pair)) (maru-proper? (maru-cdr pair)))
        (t (assert (maru-atom? (maru-cdr pair)))
           nil)))

(defun maru-tfuncs ()
  (make-tfuncs :car     #'maru-car
               :cdr     #'maru-cdr
               :cons    #'mk-pair
               :null    #'maru-nil?
               :nil     #'maru-nil
               :atom    #'maru-atom?
               :listp   #'maru-list?
               :proper? #'maru-proper?))

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
    (maru-define ctx (maru-intern ctx "or")
                     (mk-fixed #'maru-primitive-or))
    (maru-define ctx (maru-intern ctx "not")
                     (mk-fixed #'maru-primitive-not))
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
                     (mk-pform #'maru-primitive-set))
    (maru-define ctx (maru-intern ctx "seth")
                     (mk-fixed #'maru-primitive-seth))
    (maru-define ctx (maru-intern ctx "pair?")
                     (mk-expr #'maru-primitive-pair?))
    (maru-define ctx (maru-intern ctx "symbol?")
                     (mk-expr #'maru-primitive-symbol?))
    (maru-define ctx (maru-intern ctx "type-of")
                     (mk-expr #'maru-primitive-type-of))
    (maru-define ctx (maru-intern ctx "apply")
                     (mk-expr #'maru-primitive-apply))
    (maru-define ctx (maru-intern ctx "eval")
                     (mk-expr #'maru-primitive-eval))
    (maru-define ctx (maru-intern ctx "print")
                     (mk-expr #'maru-primitive-print))
    (maru-define ctx (maru-intern ctx "dump")
                     (mk-expr #'maru-primitive-dump))
    ;; extension
    (maru-define ctx (maru-intern ctx "_list")
                     (mk-expr #'maru-primitive-_list))
    ;; strings
    (maru-define ctx (maru-intern ctx "string")
                     (mk-expr #'maru-primitive-string))
    (maru-define ctx (maru-intern ctx "string-length")
                     (mk-expr #'maru-primitive-string-length))
    (maru-define ctx (maru-intern ctx "string-at")
                     (mk-expr #'maru-primitive-string-at))
    (maru-define ctx (maru-intern ctx "set-string-at")
                     (mk-expr #'maru-primitive-set-string-at))
    (maru-define ctx (maru-intern ctx "string->symbol")
                     (mk-expr #'maru-primitive-string->symbol))
    (maru-define ctx (maru-intern ctx "symbol->string")
                     (mk-expr #'maru-primitive-symbol->string))

    (maru-define ctx (maru-intern ctx "form")
                     (mk-expr #'maru-primitive-form))
    ;; arrays
    (maru-define ctx (maru-intern ctx "array")
                     (mk-expr #'maru-primitive-array))
    (maru-define ctx (maru-intern ctx "array-length")
                     (mk-expr #'maru-primitive-array-length))
    (maru-define ctx (maru-intern ctx "array-at")
                     (mk-expr #'maru-primitive-array-at))
    (maru-define ctx (maru-intern ctx "set-array-at")
                     (mk-expr #'maru-primitive-set-array-at))
    (maru-define ctx (maru-intern ctx "array?")
                     (mk-expr #'maru-primitive-array?))
    ;; ``raw'' memory
    (maru-define ctx (maru-intern ctx "allocate")
                     (mk-expr #'maru-primitive-allocate))
    (maru-define ctx (maru-intern ctx "set-oop-at")
                     (mk-expr #'maru-primitive-set-oop-at))
    (maru-define ctx (maru-intern ctx "oop-at")
                     (mk-expr #'maru-primitive-oop-at))
    ;; exit program
    (maru-define ctx (maru-intern ctx "exit")
                     (mk-expr #'maru-primitive-exit))
    (maru-define ctx (maru-intern ctx "abort")
                     (mk-expr #'maru-primitive-abort))

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
  (cond ((null list) (maru-nil))
        ((atom list) list)
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

; form
(defun maru-primitive-quote (ctx args)
  (declare (ignore ctx))
  (assert (= 1 (maru-length args)))
  (maru-car args))

; fixed
(defun maru-primitive-if (ctx args)
  (declare (ignore ctx))
  (assert (member (maru-length args) '(2 3)))
  (let ((test (maru-car  args))
        (then (maru-cadr args))
        (else (maru-cddr args)))
    (if (not (maru-nil? (nice-eval test)))
        (nice-eval then)
        ;; return ``maru-nil'' if there is no else clause
        (let ((out (maru-nil)))
          ; implicit block
          (dolist (e (maru-list-to-internal-list-1 else) out)
            (setf out (nice-eval e)))))))

; expr
(defun maru-primitive-cons (ctx args)
  (declare (ignore ctx))
  (assert (= 2 (maru-length args)))
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

; fixed
(defun maru-primitive-or (ctx args)
  (declare (ignore ctx))
  (let ((out (maru-nil)))
    (dolist (pred (maru-list-to-internal-list-1 args) out)
      (setf out (nice-eval pred))
      (when (not (maru-nil? out))
        (return out)))))

; expr
(defun maru-primitive-not (ctx args)
  (declare (ignore ctx))
  (assert (= 1 (maru-length args)))
  (mk-bool (maru-nil? (maru-car args))))

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

; pseudoform
(defun maru-primitive-set (ctx args)
  (declare (ignore ctx) (special *pseudoexpansion*))
  (assert *pseudoexpansion*)
  (assert (= 2 (maru-length args)))
  (cond ((maru-list? (maru-car args))
         (mk-pair (mk-symbol (scat "set-"
                               (object-value (maru-caar args))))
                  (maru-concat (maru-cdar args) (maru-cdr args))))
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
  (mk-bool (maru-pair? (maru-car args))))

; expr
(defun maru-primitive-symbol? (ctx args)
  (declare (ignore ctx))
  (mk-bool (maru-symbol? (maru-car args))))

; expr
(defun maru-primitive-type-of (ctx args)
  (declare (ignore ctx))
  (assert (= 1 (maru-length args)))
  (when (not (typep (maru-car args) 'raw-object))
    (error 'bad-type-of))
  (mk-number (to-string (raw-object-type (maru-car args)))))

; expr
; args <- function, [args], [environment]
(defun maru-primitive-apply (ctx args)
  (assert (and (<= (maru-length args) 3)))
               ; (typep (maru-car args) 'function-object)))
  (let ((fn (maru-car args))
        (fn-args (maru-cadr args))
        (fn-env (maru-caddr args)))
    ;; FIXME: use env if provided
    (or fn-env (assert nil))
    (maru-apply fn fn-args ctx)))

; expr
; args <- expression, [environment]
(defun maru-primitive-eval (ctx args)
  (assert (and (<= (maru-length args) 2)))
  (let ((expr (maru-car args))
        (env (maru-caddr args)))
    ;; FIXME: use env if provided
    (or env (assert nil))
    ;; expansion ---> evaluation
    (maru-expand->eval ctx expr)))

; expr
; FIXME: make nicer output/match imaru
(defun maru-primitive-print (ctx args)
  (declare (ignore ctx))
  (funcall #'format t "~A" (maru-printable-object args)))

; expr
; FIXME: make nicer output/match imaru
(defun maru-primitive-dump (ctx args)
  (declare (ignore ctx))
  (funcall #'format t "~A" (maru-printable-object args)))

; expr
(defun maru-primitive-_list (ctx args)
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
               (typep (maru-caddr args) 'char-object)))
  (let ((index (object-value (maru-cadr args)))
        (char (object-value (maru-caddr args))))
    (if (and (>= index 0) (< index (string-object-size (maru-car args))))
      (progn
        (setf (elt (object-value (maru-car args)) index) char)
        (maru-car args))
      (maru-nil))))

; expr
; > IDL: imaru implementation ignores extra args
(defun maru-primitive-string->symbol (ctx args)
  (cond ((zerop (maru-length args)) (maru-nil))
        ((typep (maru-car args) 'symbol-object) (maru-car args))
        ((typep (maru-car args) 'string-object)
         ;; don't copy the null terminator
         (maru-intern ctx (object-value
                            (maru-string-to-symbol (maru-car args)))))
        (t (maru-nil))))

; expr
; > IDL: imaru implementation ignores extra args
(defun maru-primitive-symbol->string (ctx args)
  (declare (ignore ctx))
  (cond ((zerop (maru-length args)) (maru-nil))
        ((typep (maru-car args) 'string-object) (maru-car args))
        ((typep (maru-car args) 'symbol-object)
         (mk-string :value (object-value (maru-car args))))
        (t (maru-nil))))

; expr
(defun maru-primitive-form (ctx args)
  (declare (ignore ctx))
  (assert (and (= 1 (maru-length args))
               (typep (maru-car args) 'runtime-closure-object)))
  (mk-form (maru-car args)))

; expr
; array argument is optional; default to size 0
; IDL: imaru will take any arguments to 'array'; if the first argument
; isn't a long it will create a size 0 array
(defun maru-primitive-array (ctx args)
  (declare (ignore ctx))
  (assert (and (<= (maru-length args) 1)))
  (if (zerop (maru-length args))
      (mk-array 0)
      (mk-array (object-value (maru-car args)))))

; expr
(defun maru-primitive-array-length (ctx args)
  (declare (ignore ctx))
  (assert (and (= 1 (maru-length args))
               (typep (maru-car args) 'array-object)))
  (mk-number
    (to-string (length (array-object-elements (maru-car args))))))

; expr
(defun maru-primitive-array-at (ctx args)
  (declare (ignore ctx))
  (assert (and (= 2 (maru-length args))
               (typep (maru-car args) 'array-object)
               (typep (maru-cadr args) 'number-object)))
  (let ((arr (array-object-elements (maru-car args)))
        (index (object-value (maru-cadr args))))
    (if (>= index (length arr))
        (maru-nil) ; return nil if out of bounds
        (svref arr index))))

; expr
(defun maru-primitive-set-array-at (ctx args)
  (declare (ignore ctx))
  (assert (and (= 3 (maru-length args))
               (typep (maru-car args) 'array-object)
               (typep (maru-cadr args) 'number-object)))
  (let ((index (object-value (maru-cadr args))))
    ;; handle array resizing
    ;; > FIXME: maybe should use fill pointer + vector-push-extend
    (when (>= index (length (array-object-elements (maru-car args))))
        (let ((arr (array-object-elements (maru-car args))))
          (setf (array-object-elements (maru-car args))
                (init-vector (1+ index) :initial-element (maru-nil)))
          (copy-vector (array-object-elements (maru-car args))
                       arr)))
    (setf (svref (array-object-elements (maru-car args))
                  (object-value (maru-cadr args)))
          (maru-caddr args))))

; expr
; > imaru ignores extra arguments
(defun maru-primitive-array? (ctx args)
  (declare (ignore ctx))
  (assert (and (= 1 (maru-length args))))
  (mk-bool (maru-array? (maru-car args))))

; expr
(defun maru-primitive-allocate (ctx args)
  (declare (ignore ctx))
  (assert (= 2 (maru-length args)))
  ;; return nil if either argument is not a number (long)
  (when (not (and (typep (maru-car args) 'number-object)
                  (typep (maru-cadr args) 'number-object)))
    (return-from maru-primitive-allocate (maru-nil)))
  (mk-raw (object-value (maru-car args)) (object-value (maru-cadr args))))

; expr
(defun maru-primitive-set-oop-at (ctx args)
  (declare (ignore ctx))
  (assert (= 3 (maru-length args)))
  (let ((raw (maru-car args))
        (index (maru-cadr args)))
    ;; fail if we try to use set-oop-at on non raw objects
    (assert (typep raw 'raw-object))
    ;; return nil if index argument is not a number (long)
    (when (not (typep index 'number-object))
      (return-from maru-primitive-set-oop-at (maru-nil)))
    (let ((native-index (object-value index))
          (mem (raw-object-mem raw)))
      ;; return nil if index is out of range
      (when (not (and (>= native-index 0) (< native-index (length mem))))
        (return-from maru-primitive-set-oop-at (maru-nil)))
      (setf (svref mem native-index) (maru-caddr args)))))

; expr
(defun maru-primitive-oop-at (ctx args)
  (declare (ignore ctx))
  (assert (= 2 (maru-length args)))
  (let ((raw (maru-car args))
        (index (maru-cadr args)))
    ;; accout for the imaru nil exception
    (when (maru-nil? (maru-car args))
      (return-from maru-primitive-oop-at (maru-nil)))
    ;; fail if we try to use set-oop-at on non raw objects (other than
    ;; nil)
    (assert (typep raw 'raw-object))
    ;; return nil if index argument is not a number (long)
    (when (not (typep index 'number-object))
      (return-from maru-primitive-oop-at (maru-nil)))
    (let ((native-index (object-value index))
          (mem (raw-object-mem raw)))
      ;; return nil if index is out of range
      (when (not (and (>= native-index 0) (< native-index (length mem))))
        (return-from maru-primitive-oop-at (maru-nil)))
      (svref mem native-index))))

; expr
(defun maru-primitive-exit (ctx args)
  (declare (ignore ctx))
  (let ((code (if (typep (maru-car args) 'number-object)
                  (maru-car args)
                  (mk-number "0"))))
    (error 'exit-program-signal :code code)))

; expr
(defun maru-primitive-abort (ctx args)
  (declare (ignore ctx args))
  (format t "aborted~%")
  (error 'exit-program-signal :code 1))


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

(defmethod maru-cdar (maru-list)
  (maru-cdr (maru-car maru-list)))

(defmethod maru-cddr (maru-list)
  (maru-cdr (maru-cdr maru-list)))

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

(defmethod maru-concat ((lhs list-object) (rhs list-object))
  (if (maru-nil? lhs)
      rhs
      (mk-pair (maru-car lhs) (maru-concat (maru-cdr lhs) rhs))))

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

(defun maru-string-to-symbol (maru-string)
  (assert (typep maru-string 'string-object))
  (let ((val (object-value maru-string)))
    ;; care null terminator
    (assert (char= #\Null (aref val (1- (length val)))))
    (mk-symbol (subseq val 0 (1- (length val))))))

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

(defun maru-list-onto-array (list array &key (index 0))
  (cond ((= index (length list)) array)
        ((> index (length list)) (error "bad index"))
        ((> index (length array)) (error "array too small"))
        (t (setf (aref array index) (nth index list))
           (maru-list-onto-array list array :index (1+ index)))))

(defun mk-array (size &rest elements)
  (make-instance 'array-object
    :elements (maru-list-onto-array
                elements (make-array size :initial-element (maru-nil)))))

(defclass abstract-function-object (basic-object)
  ())

(defclass runtime-closure-object (abstract-function-object)
  ((src :accessor runtime-closure-object-src
        :initarg  :src)
   (ctx :accessor runtime-closure-object-ctx
        :initarg  :ctx)))

(defun mk-closure (ctx src)
  (make-instance 'runtime-closure-object :ctx ctx :src src))

(defclass function-object (abstract-function-object)
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

(defclass pseudoform-object (function-object)
  ())

(defun mk-pform (fn)
  (make-instance 'pseudoform-object :function fn))

(defclass raw-object (basic-object)
  ((type :accessor raw-object-type
         :initarg  :type)
   (mem  :accessor raw-object-mem
         :initarg  :mem)))

(defgeneric maru-apply (fn args &optional ctx)
  (:method ((fn runtime-closure-object) (args list-object) &optional ctx)
    (declare (ignore ctx))
    ;; FIXME: ignores ctx parameter
    (cdr (pass fn 'eval args)))
  (:method ((fn function-object) (args list-object) &optional ctx)
    (assert (member (type-of (function-object-fn fn))
                    '(runtime-closure-object function)
                    :test #'string=))
    ;; FIXME: may eat a lot of undesired/incorrect behavior?
    (maru-apply (function-object-fn fn) args ctx))
  (:method ((fn function) (args list-object) &optional ctx)
    (funcall fn ctx args)))

(defun mk-raw (type size)
  (make-instance 'raw-object
    :type type
    :mem (init-vector size :initial-element (maru-nil))))

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
  (:method ((lhs array-object) (rhs array-object))
    (eq-vector (array-object-elements lhs) (array-object-elements rhs)
               :test #'eq-object))
  ;; raw mem
  (:method ((lhs raw-object) (rhs raw-object))
    (and (eql (raw-object-type lhs) (raw-object-type rhs))
         (eq-vector (raw-object-mem lhs) (raw-object-mem rhs)
                    :test #'eq-object)))
  ;; catch all
  (:method (lhs rhs)
    nil))
  

(defmethod maru-nil? ((object basic-object))
  (eq-object object (maru-nil)))

(defgeneric maru-pair? (object)
  (:method ((object basic-object))
    nil)
  (:method ((object pair-object))
    t))

(defgeneric maru-symbol? (object)
  (:method ((object basic-object))
    nil)
  (:method ((object symbol-object))
    t))

(defgeneric maru-array? (object)
  (:method ((object basic-object))
    nil)
  (:method ((object array-object))
    t))

;;; sexpr : should be a (possibly nested) list of string literals
(defun untype-everything (sexpr)
  (rude-tree-map #'(lambda (string) (mk-untyped string)) sexpr))

(defun type-it (ctx object)
  (let* ((val (object-value object))
         (len (length val))
         (first-char (char val 0)))
    (cond ((char= #\" first-char)                   ; string
           (mk-string :value (subseq val 1 (1- len))))
          ((or (digit-char-p first-char)
               ;; account for negative numbers
               (and (char= #\- first-char)
                    (> (length val) 1)
                    (digit-char-p (char val 1))))
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

(defun mapleaves (fn list)
  (assert (listp list))
  (labels ((do-work (e)
             (cond ((null e) nil)
                   ((atom e) (funcall fn e))
                   (t (mapleaves fn e)))))
    (cons (do-work (car list)) (do-work (cdr list)))))

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
  `(nil . ,(cons (transform (maru-typer) list *ctx*) args)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;  maru evalutator transformer
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; > hardcoded semantics for evaluation composition

;; FIXME: implement
(defmethod fetch-applicator ((object basic-object))
  (declare (special *ctx*))
  (when (typep object 'raw-object)
    (let ((apps (array-object-elements
                  (maru-lookup *ctx* (mk-symbol "*applicators*")))))
      (when (not (maru-nil? (svref apps (raw-object-type object))))
        (return-from fetch-applicator
          (svref apps (raw-object-type object))))))
  nil)

;;;;;;;;;; basic object ;;;;;;;;;;
;;; we could support *evaluators* and *applicators* here
;;; > if an *evaluator* exists; don't talk to the arguments and call it
;;;   from ``pass''
;;; > if an *applicator* exists; evaluate the arguments and call it from
;;;   ``pass''
; > currently only support *applicators*

;; if a type does not have a specific evaluation semantic; it just
;; evaluates to itself
(defmethod inform ((object basic-object)
                   (transformer-name (eql 'eval))
                   (whatami (eql 'arg)))
  `(nil . ,object))

(defmethod inform ((object basic-object)
                   (transformer-name (eql 'eval))
                   (whatami (eql 'lead)))
  (error (format nil "implement eval inform for ~A lead~%"
                 (type-of object))))

;; FIXME: implement *evaluators*
(defmethod inform :around ((object basic-object)
                           (transformer-name (eql 'eval))
                           (whatami (eql 'lead)))
  ; (cond ((fetch-applicator object) nil)
        ; (t (assert (next-method-p)) (call-next-method))))
  (assert (next-method-p)) (call-next-method))

(defmethod pass ((object basic-object)
                 (trasformer-name (eql 'eval))
                 (args list-object))
  (error (format nil "implement eval pass for ~A~%"
                 (type-of object))))

(defmethod pass :around ((object basic-object)
                         (transformer-name (eql 'eval))
                         (args list-object))
  (declare (special *ctx*))
  (let ((applicator (fetch-applicator object)))
    (cond (applicator `(nil . ,(maru-apply applicator args *ctx*)))
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
    `(nil . ,(maru-apply fn args *ctx*))))


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
    `(nil . ,(maru-apply fn args *ctx*))))

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
    (let* ((src (runtime-closure-object-src object))
           (params (maru-car src))
           (values args))
      (do ((_  nil (setf params (maru-cdr params)))
           (__ nil (setf values (maru-cdr values))))
          ((not (maru-pair? params)) nil)
        ;; too few arguments?
        (assert (not (maru-nil? values)))
        (maru-define-new-binding
          child-ctx (maru-car params) (maru-car values)))
      ;; lambda list is a symbol or is improper; all remaining args bind
      ;; to the remaining param
      ;; > (lambda args args)
      ;; > (lambda (a b . c) ...)
      (when (typep params 'symbol-object)
            (maru-define-new-binding
              child-ctx params values)
            (setf params (maru-nil))
            (setf values (maru-nil)))
      (assert (and (maru-nil? params) (maru-nil? values)))
    ;; apply the function in the lexical env
    `(nil . ,(nice-eval (maru-cadr (runtime-closure-object-src object))
                        :_ctx child-ctx)))))

;;;;;;;;;; number object ;;;;;;;;;;

(defmethod inform ((object number-object)
                   (transformer-name (eql 'eval))
                   (whatami (eql 'arg)))
  `(nil . ,object))

;; FIXME: support lead numbers
(defmethod inform ((object number-object)
                   (transformer-name (eql 'eval))
                   (whatami (eql 'lead)))
  (error "numbers shouldn't be lead!"))

(defmethod pass ((object number-object)
                 (transformer-name (eql 'eval))
                 (args list-object))
  (error "numbers shouldn't be lead!"))

;;;;;;;;;; form object ;;;;;;;;;;

(defmethod inform ((object form-object)
                   (transformer-name (eql 'eval))
                   (whatami (eql 'arg)))
  (error "no expand args at eval time"))
  ; `(nil . ,object))

(defmethod inform ((object form-object)
                   (transformer-name (eql 'eval))
                   (whatami (eql 'lead)))
  (error "no expand leads at eval time"))
  ; nil)

(defmethod pass ((object form-object)
                 (transformer-name (eql 'eval))
                 (args list-object))
  (error "no expand passing at eval time"))
  ; `(nil . ,(mk-pair object args)))

;;;;;;;;;; raw object ;;;;;;;;;;

(defmethod inform ((object raw-object)
                   (transformer-name (eql 'eval))
                   (whatami (eql 'arg)))
  `(nil . ,object))

(defmethod inform ((object raw-object)
                   (transformer-name (eql 'eval))
                   (whatami (eql 'lead)))
  nil)

(defmethod pass ((object raw-object)
                 (transformer-name (eql 'eval))
                 (args list-object))
  `(nil . ,(mk-pair object args)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; maru pseudoexpansion transformer
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparameter *pseudoexpansion* nil)

(defmethod inform ((object basic-object)
                   (transformer-name (eql 'pseudoexpand))
                   (whatami (eql 'arg)))
  (let ((*pseudoexpansion* t))
    (declare (special *pseudoexpansion*))
    (inform object 'expand whatami)))

(defmethod inform ((object basic-object)
                   (transformer-name (eql 'pseudoexpand))
                   (whatami (eql 'lead)))
  (let ((*pseudoexpansion* t))
    (declare (special *pseudoexpansion*))
    (inform object 'expand whatami)))

(defmethod pass ((object basic-object)
                 (trasformer-name (eql 'pseudoexpand))
                 (args list-object))
  (let ((*pseudoexpansion* t))
    (declare (special *pseudoexpansion*))
    (pass object 'expand args)))

;;;;;;;;;;; pseudoform ;;;;;;;;;;;;;;

(defmethod pass ((object pseudoform-object)
                 (transformer-name (eql 'pseudoexpand))
                 (args list-object))
  (let ((*pseudoexpansion* t))
    (declare (special *pseudoexpansion*))
    (form-helper object transformer-name args)))


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
  (let ((binding (maru-lookup *ctx* object))
        ;; HACK
        (real-transformer-name
          (if *pseudoexpansion* 'pseudoexpand transformer-name)))
    (if binding
        (let ((*forwarding-symbol* object))
          (declare (special *forwarding-symbol*))
          (pass binding real-transformer-name args))
        `(nil . ,(tcons object args)))))


;;;;;;;;;; form object ;;;;;;;;;;

(defmethod inform ((object form-object)
                   (transformer-name (eql 'expand))
                   (whatami (eql 'arg)))
  (declare (special *forwarding-symbol*))
  (error "form-objectz should not be arguments! ~A"
         (maru-printable-object *forwarding-symbol*)))

;; do not expand a macros arguments behind it's back
(defmethod inform ((object form-object)
                   (transformer-name (eql 'expand))
                   (whatami (eql 'lead)))
  (declare (special *forwarding-object*))
  nil)

(defun form-helper (fn transformer-name args)
  (declare (special *ctx* *tfuncs*))
  ;; only use this with macros/pmacros
  (assert (member transformer-name '(expand pseudoexpand)
                  :test #'string=))
  (let ((*forwarding-symbol* nil))
    (declare (special *forwarding-symbol*))
    ;; ???: we ignore the ctx attached to the macro lambda
    `(nil . ,(transform (make-transformer :name transformer-name)
                        (maru-apply fn args *ctx*)
                        *ctx*
                        :tfuncs *tfuncs*))))

(defmethod pass ((object form-object)
                 (transformer-name (eql 'expand))
                 (args list-object))
  (form-helper object transformer-name args))

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

;;;;;;;;;; fixed lead ;;;;;;;;;;

(defmethod inform ((object fixed-object)
                   (transformer-name (eql 'expand))
                   (whatami (eql 'lead)))
  (declare (special *forwarding-symbol*))
  ;; HACK.
  (if *forwarding-symbol*
    (not (eq-object (mk-symbol "quote") *forwarding-symbol*))
    t))


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

(defmacro must-signal (condition &rest body)
  `(handler-case
     (progn
       ,@body
       nil)
     (,condition (e)
        (progn
          (noop e)
          t))))

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

(deftest test-dot
  (let ((src "'(1 . (2 . (3 . 4)))"))
    (equal '("quote" . (("1" . ("2" . ("3" . "4"))) . nil))
           (tokenize (next-char-factory src) '((#\' . quote-handler))))))

(deftest test-dot-2
  (let ((src "'((a . b) . (1 . (($ . 3) . 4)))"))
    (equal '("quote" . ((("a" . "b") . ("1" . (("$" . "3") . "4"))). nil))
           (tokenize (next-char-factory src) '((#\' . quote-handler))))))

(deftest test-dot-3
  (let ((src "'(a b (c d e . f))"))
    (equal '("quote" ("a" "b" ("c" "d" "e" . "f")))
           (tokenize (next-char-factory src) '((#\' . quote-handler))))))

(deftest test-too-many-with-dots
  (let ((src "'(a . (b . c . d))"))
    (must-signal token-error
      (tokenize (next-char-factory src) '((#\' . quote-handler))))))

(deftest test-not-enough-with-dots
  (let ((src "'( a . ( b . (. e)))"))
    (must-signal token-error
      (tokenize (next-char-factory src) '((#\' . quote-handler))))))

(deftest test-no-token
  (let ((src0 "")
        (src1 (scat "   " #\Tab #\Newline "   ")))
    (and (must-signal token-error
           (tokenize (next-char-factory src0) '((#\' . quote-handler))))
         (must-signal token-error
           (tokenize (next-char-factory src1)
                     '((#\' . quote-handler)))))))

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

(deftest test-doublequote-escapes
  (let ((ctx (maru-initialize))
        (src "(define b \"kewl\\\"bro\\\"\")")
        (typed-expr
          (mk-list (mk-symbol "define") (mk-symbol "b")
                   (mk-string :value "kewl\"bro\""))))
    (eq-object typed-expr (type-expr ctx src))))

(deftest test-doublequote-bug-leading-string-space
  (let ((ctx (maru-initialize))
        (src "(define d \"  this\")")
        (typed-expr
          (mk-list (mk-symbol "define") (mk-symbol "d")
                   (mk-string :value "  this"))))
    (eq-object typed-expr (type-expr ctx src))))

(deftest test-doublequote-bug-trailing-string-space
  (let ((ctx (maru-initialize))
        (src "(define a \"this \")")
        (typed-expr
          (mk-list (mk-symbol "define") (mk-symbol "a")
                   (mk-string :value "this "))))
    (eq-object typed-expr (type-expr ctx src))))

(deftest test-doublequote-bug-internal-string-space
  (let ((ctx (maru-initialize))
        (src "(define a \"this that\")")
        (typed-expr
          (mk-list (mk-symbol "define") (mk-symbol "a")
                   (mk-string :value "this that"))))
    (eq-object typed-expr (type-expr ctx src))))

(deftest test-next-char-factory-peek-bug
  (let ((next-char-fn
          (next-char-factory "something")))
    (progn (equal (funcall next-char-fn) #\s)
         (equal (funcall next-char-fn 'peek) #\o)
         (equal (funcall next-char-fn 'peek) #\o)
         (equal (funcall next-char-fn) #\o))))

(deftest test-type-transformer
  (let ((type-transformer (maru-typer))
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
  (let ((type-transformer (maru-typer))
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
  (let ((type-transformer (maru-typer))
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
  (let ((type-transformer (maru-typer))
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
         (type-transformer (maru-typer))
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
         (type-transformer (maru-typer))
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
                      (#\` . quasiquote-handler)
                      (#\" . doublequote-handler))))
    (untype-everything
      (tokenize (next-char-factory src) read-table))))

(defun type-expr (ctx src)
  (transform (maru-typer) (untype-expr src) ctx))

(defun maru-expand->eval (ctx expr)
  (let ((expand-transformer (make-transformer :name 'expand))
        (pseudoexpand-transformer (make-transformer :name 'pseudoexpand))
        (eval-transformer (make-transformer :name 'eval))
        (expanded-expr nil)
        (pexpanded-expr nil)
        (evald-expr nil))
    (setf expanded-expr
          (transform expand-transformer
                     expr
                     ctx
                     :tfuncs (maru-tfuncs)))
    ; (when (atom expanded-expr)
        ; (format t "EXPAND: ~A~%" (maru-printable-object expanded-expr)))
    (setf pexpanded-expr
          (transform pseudoexpand-transformer
                     expanded-expr
                     ctx
                     :tfuncs (maru-tfuncs)))
    ; (when (atom expanded-expr)
        ; (format t "PEXPAND: ~A~%"
                  ; (maru-printable-object pexpanded-expr)))
    (setf evald-expr
          (transform eval-transformer
                     pexpanded-expr
                     ctx
                     :tfuncs (maru-tfuncs)))
    ; (when (atom evald-expr)
        ; (format t "EVALD : ~A~%" (maru-printable-object evald-expr)))
    evald-expr))

(defun maru-all-transforms (ctx src)
  (let ((typed-expr (type-expr ctx src)))
    ; (when (atom typed-expr)
        ; (format t "TYPED: ~A~%" (maru-printable-object typed-expr)))
    (maru-expand->eval ctx typed-expr)))

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

(deftest test-maru-primitive-if-empty-else
  (let ((ctx (maru-initialize))
        (src "(if () 10)"))
    (eq-object (maru-nil)
               (maru-all-transforms ctx src))))

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

(deftest test-fetch-applicator
  "get an applicator for some object"
  (let ((*ctx* (maru-initialize))
        (src "(block
                (define a (allocate 2 2))
                (set-array-at *applicators*
                              (type-of a)
                              (lambda args 2)))"))
    (declare (special *ctx*))
    (and (null (fetch-applicator (mk-number "1")))
         (null (fetch-applicator (mk-raw 2 2)))
         (progn
           (maru-all-transforms *ctx* src)
           (and (null (fetch-applicator (mk-number "500")))
                (typep (fetch-applicator (mk-raw 2 2))
                       'runtime-closure-object))))))

(deftest test-maru-applicators
  (let ((ctx (maru-initialize))
        (src "(block
                (define a (allocate 3 3))
                (set-array-at *applicators*
                              (type-of a)
                              (lambda args (cons 55 args))))")
        (use-it "(cons (a 1 2 3) (a \"this\"))"))
    (maru-all-transforms ctx src)
    (eq-object (mk-pair (mk-list (mk-number "55")
                                 (mk-number "1")
                                 (mk-number "2")
                                 (mk-number "3"))
                        (mk-list (mk-number "55")
                                 (mk-string :value "this")))
               (maru-all-transforms ctx use-it))))

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
    (maru-intern child-ctx "somethang")
    ;; global
    (maru-define child-ctx (maru-intern child-ctx "theother")
                           (mk-number "16"))
         ;; added stuff to parent env?
    (and (not (binding-exists? ctx "this"))
         (member (mk-symbol "this") (maru-context-symbols ctx)
                 :test #'eq-object)
         (binding-exists? ctx "that")
         (not (binding-exists? ctx "somethang"))
         (binding-exists? ctx "theother")
         ; child symbols still valid
         (member (mk-symbol "somethang") (maru-context-symbols ctx)
                 :test #'eq-object)
         (member (mk-symbol "theother") (maru-context-symbols ctx)
                 :test #'eq-object)
         ;; added stuff to child env
         (not (binding-exists? child-ctx "somethang"))
         (member (mk-symbol "somethang") (maru-context-symbols child-ctx)
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

(deftest test-maru-lambda-improper-parameters
  (let* ((ctx (maru-initialize))
         (src "(define fn
                 (lambda (a b . c)
                   (cons (+ a b) c)))")
         (use-it "(fn 1 2 3 4 5)"))
    (maru-all-transforms ctx src)
    (eq-object (mk-list (mk-number "3") (mk-number "3")
                        (mk-number "4") (mk-number "5"))
               (maru-all-transforms ctx use-it))))

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

(defun concat-string-src ()
  "(define concat-string
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

(deftest test-maru-concat-string
  (let ((ctx (maru-initialize))
        (code (concat-string-src))
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
        (src "(_list 1 2 (_list \"three\" (_list 4)) \"five\")"))
    (eq-object (mk-list (mk-number "1") (mk-number "2")
                        (mk-list (mk-string :value "three")
                                 (mk-list (mk-number "4")))
                        (mk-string :value "five"))
               (maru-all-transforms ctx src))))

(deftest test-maru-array-primitive
  (let ((ctx (maru-initialize))
        (src "(array 5)"))
    (eq-object (mk-array 5)
               (maru-all-transforms ctx src))))

(deftest test-maru-array-primitive-default-bug
  (let ((ctx (maru-initialize))
        (src "(array)"))
    (eq-object (mk-array 0)
               (maru-all-transforms ctx src))))

(deftest test-maru-set-array-at-primitive
  (let ((ctx (maru-initialize))
        (src "(block
                (define a (array 5))
                (set-array-at a 2 3))")
        (use-it "(block a)"))
    (and (eq-object (mk-number "3")
                    (maru-all-transforms ctx src))
         (eq-object (mk-array 5 (maru-nil) (maru-nil) (mk-number "3")
                                (maru-nil) (maru-nil))
                    (maru-all-transforms ctx use-it)))))

(deftest test-maru-array-auto-resizing
  "arrays automatically resize when an out of bounds index is set"
  (let ((ctx (maru-initialize))
        (src "(block
                (define a (array 2))
                (set-array-at a 4 'twelve))")
        (use-it "(block a)"))
    (maru-all-transforms ctx src)
    (and (eq-object (mk-array 5 (maru-nil) (maru-nil) (maru-nil)
                                (maru-nil) (mk-symbol "twelve"))
                    (maru-all-transforms ctx use-it)))))

(deftest test-maru-array-at-primitive
  (let ((ctx (maru-initialize))
        (src "(block
                (define a (array 5))
                (set-array-at a 3 'sunshine)
                (array-at a 3))"))
    (eq-object (mk-symbol "sunshine")
               (maru-all-transforms ctx src))))

;; for testing
(defun quasiquote-src ()
  "(block
     (define cadr
       (lambda (l)
         (car (cdr l))))
     (define quasiquote
       (form
         (let ((qq-list) (qq-element) (qq-object))
           (set qq-list (lambda (l)
                          (if (pair? l)
                            (let ((obj (car l)))
                              (if (and (pair? obj)
                                       (= (car obj)
                                          'unquote-splicing))
                                  (if (cdr l)
                                      (_list 'concat-list
                                            (cadr obj)
                                            (qq-list (cdr l)))
                                      (cadr obj))
                                  (_list 'cons
                                        (qq-object obj)
                                        (qq-list (cdr l)))))
                            (_list 'quote l))))
           (set qq-element (lambda (l)
                             (let ((head (car l)))
                               (if (= head 'unquote)
                                   (cadr l)
                                   (qq-list l)))))
           (set qq-object (lambda (object)
                            (if (pair? object)
                                (qq-element object)
                                (_list 'quote object))))
           (lambda (expr)
             (qq-object expr))))))")

(defun define-function-src ()
  '("(define define-form
       (form
         (lambda (name args . body)
           `(define ,name (form (lambda ,args ,@body))))))"
    "(define-form define-function (name args . body)
       `(define ,name (lambda ,args ,@body)))"))

(defun list-length-src ()
  "(define-function list-length (list)
     (if (pair? list)
         (+ 1 (list-length (cdr list)))
         0))")

(deftest test-maru-define-form
  (let ((ctx (maru-initialize))
        (qq-src (quasiquote-src))
        (def-src (define-function-src))
        (ll-src (list-length-src))
        (use-it "(cons (list-length '()) (list-length '(0 1 2 3)))"))
    (maru-all-transforms ctx qq-src)
    (dolist (d def-src)
      (maru-all-transforms ctx d))
    (maru-all-transforms ctx ll-src)
    (eq-object (mk-pair (mk-number "0") (mk-number "4"))
               (maru-all-transforms ctx use-it))))

(deftest test-maru-map
  (let ((ctx (maru-initialize))
        (qq-src (quasiquote-src))
        (def-src (define-function-src))
        (src "(define-function map (function list)
                (if (pair? list)
                    (let ((head (function (car list))))
                      (cons head (map function (cdr list))))))")
        (use-it "(block
                   (define f (lambda (a) (+ 1 a)))
                   (map f '(1 2 3)))"))
    (maru-all-transforms ctx qq-src)
    (dolist (d def-src)
      (maru-all-transforms ctx d))
    (maru-all-transforms ctx src)
    (eq-object (mk-list (mk-number "2") (mk-number "3") (mk-number "4"))
               (maru-all-transforms ctx use-it))))

;; FIXME: this seems to be close; but not quite right, hard to test
(deftest test-maru-quasiquote
  (let ((ctx (maru-initialize))
        (src (quasiquote-src))
        (use-it-0 "`(1 (2) 3)")
        (use-it-1 "`9"))
    (maru-all-transforms ctx src)
    (and (eq-object (mk-list (mk-number "1")
                             (mk-list (mk-number "2"))
                             (mk-number "3"))
                    (maru-all-transforms ctx use-it-0))
         (eq-object (mk-number "9")
                    (maru-all-transforms ctx use-it-1)))))

;; FIXME: macro expansion is broken
(deftest test-maru-quasiquote-2
  (let ((ctx (maru-initialize))
        (src (quasiquote-src))
        (use-it "``5"))
    (maru-all-transforms ctx src)
    (eq-object (mk-list (mk-symbol "quasiquote") (mk-number "5"))
               (maru-all-transforms ctx use-it))))

(deftest test-maru-quasiquote-3
  (let ((ctx (maru-initialize))
        (src (quasiquote-src))
        (use-it "`,@('thing 1 2 3)"))
    (maru-all-transforms ctx src)
    (eq-object (mk-list (mk-symbol "unquote-splicing")
                        (mk-list (mk-list
                                   (mk-symbol "quote")
                                   (mk-symbol "thing"))
                                 (mk-number "1")
                                 (mk-number "2")
                                 (mk-number "3")))
               (maru-all-transforms ctx use-it))))

(deftest test-maru-%list->array
  (let ((ctx (maru-initialize))
        (src "(define %list->array
                (lambda (list index)
                  (if (pair? list)
                      (let ((a (%list->array (cdr list) (+ 1 index))))
                        (set-array-at a index (car list))
                        a)
                      (array index))))")
        (use-it "(block
                   (define l '(1 2 3 (4) 5))
                   (%list->array l 0))"))
    (maru-all-transforms ctx src)
    (eq-object (mk-array 5 (mk-number "1")
                           (mk-number "2")
                           (mk-number "3")
                           (mk-list (mk-number "4"))
                           (mk-number "5"))
               (maru-all-transforms ctx use-it))))

(defun concat-symbol-src ()
  "(define concat-symbol
     (lambda (x y)
       (string->symbol
         (concat-string (symbol->string x)
                        (symbol->string y)))))")

(defun list-src ()
  "(define list (lambda args args))")

(defun let*-src ()
  '("(define-function %let* (bindings body)
       (if (pair? (cdr bindings))
           `(let (,(car bindings)) ,(%let* (cdr bindings) body))
           `(let ,bindings ,@body)))"
    "(define-form let* bindings-body
       (%let* (car bindings-body) (cdr bindings-body)))"))

(defun maru-initialize+ ()
  (let ((ctx (maru-initialize))
        (qq-src (quasiquote-src))
        (def-src (define-function-src))
        (cs-src (concat-string-src))
        (ll-src (list-length-src))
        (csym-src (concat-symbol-src))
        (l-src (list-src)))
    (maru-all-transforms ctx qq-src)
    (dolist (d def-src)
      (maru-all-transforms ctx d))
    (maru-all-transforms ctx cs-src)
    (maru-all-transforms ctx ll-src)
    (maru-all-transforms ctx csym-src)
    (maru-all-transforms ctx l-src)
    (dolist (e (let*-src))
      (maru-all-transforms ctx e))
    ctx))

(deftest test-maru-concat-symbol
  (let ((ctx (maru-initialize+))
        (use-it "(concat-symbol 'hello 'world)"))
    (eq-object (mk-symbol "helloworld")
               (maru-all-transforms ctx use-it))))

(deftest test-maru-string->symbol-primitive-intern-bug
  "string->symbol must intern the new symbol"
  (let ((ctx (maru-initialize))
        (src "(string->symbol \"y2k\")"))
    (maru-all-transforms ctx src)
    (member (mk-symbol "y2k") (maru-context-symbols ctx)
            :test #'eq-object)))

(deftest test-maru-define-structure
  (let ((ctx (maru-initialize+))
        (src "(block
                (define %type-names (array 16))
                (define %last-type  -1)
                (define %allocate-type
                  (lambda (name)
                    (set %last-type (+ 1 %last-type))
                    (set-array-at %type-names %last-type name)
                    %last-type))
                (define %structure-sizes    (array))
                (define %structure-fields   (array))
                (define-function %make-accessor (name fields offset)
                  (if fields
                      (cons
                        `(define-form
                           ,(concat-symbol
                              name
                              (concat-symbol '- (car fields)))
                           (self)
                           (list 'oop-at self ,offset))
                         (%make-accessor name (cdr fields)
                                              (+ 1 offset)))))
                (define-function %make-accessors (name fields)
                  (%make-accessor name fields 0))
                (define-form define-structure (name fields)
                  (let ((type (%allocate-type name))
                        (size (list-length fields)))
                    (set-array-at %structure-sizes  type size)                                 (set-array-at %structure-fields type fields)
                    `(let ()
                       (define ,name ,type)
                       ,@(%make-accessors name fields))))
                (define-function new (type)
                  (allocate type (array-at %structure-sizes type))))")
        (long-struct "(define-structure <long>    (_bits))")
        (use-it "(block
                   (define l (new <long>))
                   (set (<long>-_bits l) 10)
                   (cons l (cons (oop-at l 0) (<long>-_bits l))))")
        (test-raw nil))
    (maru-all-transforms ctx src)
    (maru-all-transforms ctx long-struct)
    (setf test-raw (mk-raw 0 1))
    (setf (svref (raw-object-mem test-raw) 0) (mk-number "10"))
    (eq-object (mk-pair test-raw
                        (mk-pair (mk-number "10") (mk-number "10")))
               (maru-all-transforms ctx use-it))))

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

(deftest test-macros-simple
  (let ((ctx (maru-initialize))
        (src "(define m
                (form
                  (lambda (a)
                    '(define b 2))))")
        (use-it "(m 1)"))
    (maru-all-transforms ctx src)
    (eq-object (mk-number "2")
               (maru-all-transforms ctx use-it))))

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
                        (_list 'cons i i)))
                    (lambda ()
                        (gn (fn 5))))))")
        (use-it "(m)"))
    (maru-all-transforms ctx src)
    (eq-object (mk-pair (mk-number "50") (mk-number "50"))
               (maru-all-transforms ctx use-it))))

(deftest test-macros-2
  (let ((ctx (maru-initialize))
        (src "(define m
                (form
                  (lambda (a . b)
                    `(define ,a ',b))))")
        (src1 "(m a 1 2 3 4 5)"))
    (maru-all-transforms ctx (quasiquote-src))
    (maru-all-transforms ctx src)
    (eq-object (maru-all-transforms ctx src1)
               (mk-list (mk-number "1") (mk-number "2") (mk-number "3")
                        (mk-number "4") (mk-number "5")))))

(deftest test-macros-3
  (let ((ctx (maru-initialize))
        (src "(define m
                (form
                  (lambda (a . b)
                    `(define ,a
                       (form
                         (lambda ,b
                           (pair? (car (_list ,@b)))))))))")
        (src1 "(m something a b c d)")
        (src2 "(something '(1 2) 3 4 5)"))
    (maru-all-transforms ctx (quasiquote-src))
    (maru-all-transforms ctx src)
    (maru-all-transforms ctx src1)
    (eq-object (mk-bool t)
               (maru-all-transforms ctx src2))))

;; this is not supported by imaru quasiquote
(deftest test-macros-4
  (let ((ctx (maru-initialize))
        (src0 "(define m
                 (form
                   (lambda (a b)
                     `(define ,a
                        (form
                          (lambda (c d)
                            `(+ ,,b (+ ,c ,d))))))))")
        (src1 "(m electrifying 5)")
        (src2 "(electrifying 2 9)"))
    (declare (ignore ctx src0 src1 src2))))
#|
    nil))
    (maru-all-transforms ctx (quasiquote-src))
    (maru-all-transforms ctx src0)
    (maru-all-transforms ctx src1)
    (eq-object (mk-number "16")
               (maru-all-transforms ctx src2))))
|#

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

(deftest test-internal-list-to-maru-list-improper
  (let ((list`((,(mk-number "3") . ,(mk-number "2")) . ,(mk-number "9"))))
    (eq-object (mk-pair (mk-pair (mk-number "3") (mk-number "2"))
                        (mk-number "9"))
               (internal-list-to-maru-list list))))

(deftest test-maru-list-pair-sanity
       ;; nil and pairs are lists
  (and (maru-list? (maru-nil))
       (maru-list? (mk-pair (mk-number "3") (mk-number "4")))
       (maru-list? (mk-list (mk-number "5") (mk-number "5")))
       ;; other things are not lists
       (not (maru-list? (mk-number "12")))
       (not (maru-list? (make-instance 'basic-object)))
       ;; everything other than pairs are atoms
       (maru-atom? (maru-nil))
       (maru-atom? (mk-number "4"))
       (maru-atom? (mk-string :value "whatever"))
       (not (maru-atom? (mk-list (mk-number "4"))))
       (not (maru-atom? (mk-pair (mk-number "9") (mk-number "10"))))))

(deftest test-maru-nil-sanity
       ;; only nil is nil
  (and (maru-nil? (maru-nil))
       ;; nil is the empty list
       (maru-nil? (mk-list))
       (not (maru-nil? (mk-list "this" "that")))
       (not (maru-nil? (mk-pair (mk-number "2") (mk-number "9"))))
       (not (maru-nil? (mk-pair (maru-nil) (maru-nil))))))

(deftest test-noop-transform-improper-list
  (let-sugar (maru-tfuncs)
    (let ((noop-transformer (make-transformer :name 'noop))
          (untyped-expr (untype-everything
                          (tokenize
                            (next-char-factory "'(1 (2 . 3))")
                            '((#\' . quote-handler))))))
      (and (rude-eq-tree `(,(mk-untyped "quote")
                           (,(mk-untyped "1")
                             (,(mk-untyped "2") . ,(mk-untyped "3"))))
                          untyped-expr
                          :test #'eq-object)
           (rude-eq-tree (transform noop-transformer untyped-expr nil)
                         untyped-expr
                         :test #'eq-object)))))

;; fixme
(deftest test-noop-transform-improper-list-2
  (let-sugar (maru-tfuncs)
    (let* ((ctx (maru-initialize))
           (noop-transformer (make-transformer :name 'type))
           (src "(block
                   (define define-form
                     (form
                       (lambda (name args . body)
                         `(define ,name
                            (form (lambda ,args ,@body)))))))")
           (untyped-expr (untype-expr src)))
      (eq-object
        (mk-list
          (mk-symbol "block")
          (mk-list
            (mk-symbol "define")
            (mk-symbol "define-form")
            (mk-list
              (mk-symbol "form")
              (mk-list
                (mk-symbol "lambda")
                (mk-pair
                  (mk-symbol "name")
                  (mk-pair
                    (mk-symbol "args")
                    (mk-symbol "body")))
                (mk-list
                  (mk-symbol "quasiquote")
                  (mk-list
                    (mk-symbol "define")
                    (mk-list (mk-symbol "unquote") (mk-symbol "name"))
                    (mk-list
                      (mk-symbol "form")
                        (mk-list
                          (mk-symbol "lambda")
                          (mk-list (mk-symbol "unquote")
                                   (mk-symbol "args"))
                          (mk-list (mk-symbol "unquote-splicing")
                                   (mk-symbol "body"))))))))))
        (transform noop-transformer untyped-expr ctx)))))

(deftest test-maru-proper?
  (and (maru-proper? (mk-pair (mk-number "1") (maru-nil)))
       (maru-proper? (mk-list))
       (not (maru-proper? (mk-pair (mk-number "2") (mk-number "3"))))
       (not (maru-proper? (mk-pair (mk-number "1")
                                   (mk-pair (mk-number "9")
                                            (mk-number "99")))))))

(deftest test-imaru-list
  "uses a symbol for the lambda lists; capture all arguments"
  (let ((ctx (maru-initialize+))
        (use-it "(block
                   (define l (list 'a 'b 'c))
                   l)"))
    (eq-object (mk-list (mk-symbol "a") (mk-symbol "b") (mk-symbol "c"))
               (maru-all-transforms ctx use-it))))

(deftest test-negative-number-bug
  (let ((ctx (maru-initialize))
        (src "(define a -10)"))
    (eq-object (mk-number "-10")
               (maru-all-transforms ctx src))))

(deftest test-maru-allocate-primitive
  (let ((ctx (maru-initialize))
        (use-it "(_list (allocate 12 3) (allocate 1 '())
                        (allocate () 5) (allocate '() ()))"))
    (and (eq-object (mk-list (mk-raw 12 3) (maru-nil) (maru-nil)
                             (maru-nil))
                    (maru-all-transforms ctx use-it))
         ;; all elements should be nil
         (progn
           (maru-all-transforms ctx "(define g (allocate 3 2))")
           (and (eq-object (maru-nil)
                           (svref (raw-object-mem
                                    (maru-all-transforms ctx "(block g)"))
                                  0))
                (eq-object (maru-nil)
                           (svref (raw-object-mem
                                    (maru-all-transforms ctx "(block g)"))
                                  1)))))))

(deftest test-maru-set-oop-at-primitive
  "we only support this op with raw objects"
  (let ((ctx (maru-initialize))
        (use-it "(block
                   (define aa (allocate 0 2))
                   (set-oop-at aa 0 55))"))
    (and (eq-object (mk-number "55")
                    (maru-all-transforms ctx use-it))
         (eq-object (mk-number "55")
                    (svref (raw-object-mem
                             (maru-all-transforms ctx "(block aa)"))
                           0)))))

(deftest test-maru-set-oop-at-primitive-invalids
  (let ((ctx (maru-initialize))
        (use-it "(block
                   (define bb (allocate 8 3))
                   (set-oop-at bb 1 23))"))
    (maru-all-transforms ctx use-it)
    ;; return nil and do nothing on non integer index
    (and (eq-object (maru-nil)
                    (maru-all-transforms ctx "(set-oop-at bb \"t\" 14)"))
         ;; return nil and do nothing if index is out of bounds
         (eq-object (maru-nil)
                    (maru-all-transforms ctx "(set-oop-at bb -5 10)"))
         (eq-object (maru-nil)
                    (maru-all-transforms ctx "(set-oop-at bb 9 8)"))
         (eq-object (mk-number "23")
                    (svref (raw-object-mem
                             (maru-all-transforms ctx "(block bb)"))
                           1)))))

(deftest test-maru-oop-at-primitive
  (let ((ctx (maru-initialize))
        (use-it "(block
                   (define cc (allocate 9 5))
                   (set-oop-at cc 2 14)
                   (set-oop-at cc 4 8)
                   (cons (oop-at cc 2) (oop-at cc 4)))"))
    (and (eq-object (mk-pair (mk-number "14") (mk-number "8"))
                    (maru-all-transforms ctx use-it)))))

(deftest test-maru-oop-at-primitive-invalids
  (let ((ctx (maru-initialize))
        (use-it "(define dd (allocate 10 7))"))
    (maru-all-transforms ctx use-it)
         ;; return nil and do nothing if non integer index
    (and (eq-object (maru-nil)
                    (maru-all-transforms ctx "(oop-at dd dd)"))
         ;; return nil and do nothing if object is nil
         (eq-object (maru-nil)
                    (maru-all-transforms ctx "(oop-at '() 9)"))
         ;; return nil and do nothing if index is out of bounds
         (eq-object (maru-nil)
                    (maru-all-transforms ctx "(oop-at dd -9)"))
         (eq-object (maru-nil)
                    (maru-all-transforms ctx "(oop-at dd 24)")))))

(deftest test-maru-set-primitive-bug
  "set must handle multiple arguments to the car function"
  (let ((ctx (maru-initialize))
        (src "(block
                (define fn
                  (lambda (a b c)
                    (+ a (+ b c))))
                (define set-fn
                  (lambda (a b c d)
                    (+ a (+ b (+ c d))))))")
        (use-it "(set (fn 2 3 4) 5)"))
    (maru-all-transforms ctx src)
    (eq-object (mk-number "14")
               (maru-all-transforms ctx use-it))))

(deftest test-imaru-array->string
  (let ((ctx (maru-initialize+))
        (src "(define-function array->string (arr)
                (let* ((ind 0)
                       (lim (array-length arr))
                       (str (string lim)))
                  (while (< ind lim)
                    (set-string-at str ind (array-at arr ind))
                    (set ind (+ 1 ind)))
                  str))")
        (use-it "(block
                   (define a (array 6))
                   (set-array-at a 0 ?s) (set-array-at a 1 ?c)
                   (set-array-at a 2 ?h) (set-array-at a 3 ?o)
                   (set-array-at a 4 ?o) (set-array-at a 5 ?l)
                   (array->string a))"))
    (maru-all-transforms ctx src)
    (eq-object (mk-string :value "school")
               (maru-all-transforms ctx use-it))))

;; FIXME: handle newlines
(deftest test-imaru-println
  (let ((ctx (maru-initialize+))
        ;; modified; should use do-print where we use %print
        (src "(block
                (define %print print)
                (define print
                  (lambda args
                    (while (pair? args)
                      (%print (car args))
                      (set args (cdr args)))))
                (define println
                   (lambda args
                     (apply print args)
                     (%print \"\n\"))))")
        (use-it "(block
                   (define a 10)
                   (println \"hello \" a \"world\"))"))
    ; (declare (ignore ctx src use-it))
    (maru-all-transforms ctx src)
    ;; FIXME: test the output of some stream
    (maru-all-transforms ctx use-it)
    nil))

(deftest test-maru-exit-primitive
  (let ((ctx (maru-initialize))
        (src "(exit 2)"))
    (must-signal exit-program-signal
      (maru-all-transforms ctx src))))

(deftest test-maru-abort-primitive
  (let ((ctx (maru-initialize))
        (src "(abort \"args\" \"dont\" \"matter\")"))
    (must-signal exit-program-signal
      (maru-all-transforms ctx src))))

(deftest test-maru-or-primitive
  (let ((ctx (maru-initialize))
        (src "(cons (or () () 4) (or 2 5))"))
    (eq-object (mk-pair (mk-number "4") (mk-number "2"))
               (maru-all-transforms ctx src))))

(deftest test-maru-eval-primitive
  (let ((ctx (maru-initialize))
        (src "(block
                (define a 10)
                (cons (eval 'a) (eval '(+ 1 2))))"))
    (eq-object (mk-pair (mk-number "10") (mk-number "3"))
               (maru-all-transforms ctx src))))

(deftest test-maru-type-of-primitive
  (let ((ctx (maru-initialize)))
    (and (eq-object (mk-number "13")
                    (maru-all-transforms ctx "(type-of (allocate 13 0))"))
         (must-signal bad-type-of
           (maru-all-transforms ctx "(type-of 5)")))))

(deftest test-maru-dump-primitive
  (let ((ctx (maru-initialize))
        (src "(dump 567)"))
    (maru-all-transforms ctx src)
    nil))

(deftest test-maru-symbol?-primitive
  (let ((ctx (maru-initialize))
        (src "(cons (symbol? 'this-or-that) (symbol? ?a))"))
    (eq-object (mk-pair (mk-bool t) (mk-bool nil))
               (maru-all-transforms ctx src))))

(deftest test-maru-array?-primitive
  (let ((ctx (maru-initialize))
        (src "(cons (array? 5) (array? (array 3)))"))
    (eq-object (mk-pair (mk-bool nil) (mk-bool t))
               (maru-all-transforms ctx src))))

(deftest test-maru-not-primitive
  (let ((ctx (maru-initialize))
        (src "(cons (not ()) (not (not (not 5))))"))
    (eq-object (mk-pair (mk-bool t) (mk-bool nil))
               (maru-all-transforms ctx src))))

