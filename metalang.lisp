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
  (declare (optimize debug))
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
  (declare (optimize debug))
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
  (declare (optimize debug))
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
  (declare (optimize debug))
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

(defmethod eq-object ((lhs single-value-object) (rhs single-value-object))
  (equal (object-value lhs) (object-value rhs)))

(defmethod eq-object ((lhs list-object) (rhs list-object))
  (eq-tree (list-object-elements lhs) (list-object-elements rhs)
           :test #'eq-object))

;;; sexpr : should be a (possibly nested) list of string literals
(defun untype-everything (sexpr)
  (tree-map #'(lambda (string) (mk-untyped string)) sexpr))


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
;;;    type transformer
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmethod inform ((object untyped-object)
                   (transformer-name (eql 'type))
                   (whatami (eql 'arg)))
  (let* ((val (object-value object))
         (len (length val))
         (first-char (char val 0)))
    (cond ((char= #\" first-char)                   ; string
           (cons nil (mk-string (subseq val 1 (1- len)))))
          ((alpha-char-p first-char) (cons nil (mk-symbol val)))
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
  (cons nil (append (list (mk-symbol (object-value object))) args)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;     infrastructure
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun back-talk-arg (transformer expr)
  (declare (optimize debug))
  (assert (typep expr 'atom))
  ;; response : (transform-more? . sexpr)
  (let ((response (inform expr (transformer-name transformer) 'arg)))
    (if (car response)
        (transform transformer (cdr response) *env*)
        (cdr response))))

(defun back-talk-sexpr (transformer lead &key expr-args)
  (declare (optimize debug))
  (assert (typep expr-args 'list))
  ;; response : can-i-talk-to-your-arguments?
  (let* ((response (inform lead (transformer-name transformer) 'lead))
         (args (mapcar #'(lambda (a)
                           (if response
                               (transform transformer a *env*)
                               (identity a)))
                       expr-args)))
      ;; response : (transform-more? . sexpr)
      (let ((response-2
              (pass lead (transformer-name transformer) args)))
        (if (car response-2)
            (transform transformer (cdr response-2) *env*)
            (cdr response-2)))))

;;; transform a single expression {sexpression, atom}
(defun transform (transformer expr env)
  (let ((*env* env))
    (declare (special *env*))
    (cond ((atom expr) (back-talk-arg transformer expr))
          ((null expr) '())
          (t
            (back-talk-sexpr transformer
                             (car expr)
                             :expr-args (cdr expr))))))

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
                          (mk-symbol "sym9001"))))
    (eq-tree (transform type-transformer untyped-expr nil) typed-expr
             :test #'eq-object)))

(deftest test-type-transformer-number
  (let ((type-transformer (make-transformer :name 'type))
        (untyped-expr (untype-everything
                        (tokenize
                          (next-char-factory
                            "(trees 0x123 (green 2) 0X456)"))))
        (typed-expr (list (mk-symbol "trees") (mk-number "123" :hex t)
                          (list (mk-symbol "green") (mk-number "2"))
                          (mk-number "456" :hex t))))
    (eq-tree (transform type-transformer untyped-expr nil) typed-expr
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
                (mk-char #\!))))
    (eq-tree (transform type-transformer untyped-expr nil) typed-expr
             :test #'eq-object)))

