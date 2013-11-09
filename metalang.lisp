;;;; library for defining language semantics
;;;; Aaron Burrow : burrows.labs@gmail.com

;;;; components
;;;; > tokenizer, produces sexpressions from a string literal
;;;; > translation manager, translations against sexpressions

;;;; TODO
;;;; > How do we handle environments?

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

(defun tokenize-parenlist (next-char-fn)
  (declare (optimize debug))
  (let ((c (funcall next-char-fn))
        (exprs '()))
    (assert (char= c #\())
    (do ((char (funcall next-char-fn 'peek) (funcall next-char-fn 'peek)))
        ((char= char #\)) exprs)
      (let ((e (tokenize next-char-fn)))
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
(defun tokenize (next-char-fn)
  (declare (optimize debug))
  (let ((c (funcall next-char-fn)))
    (cond ((null c) '())
          ((char= c #\()
           (funcall next-char-fn 'unread)
           (tokenize-parenlist next-char-fn))
          ((whitespace? c) (tokenize next-char-fn))
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
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;    Transformation Manager
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; > each type of object must be able to handle each type of
;;;;   transformation

(defstruct transformer
  name)

(defclass basic-object ()
  ((value :accessor basic-object-value
          :initarg :value)))

(defclass untyped-object (basic-object)
  ())

(defun mk-untyped (value)
  (make-instance 'untyped-object :value value))

(defmethod eq-object ((lhs untyped-object) (rhs untyped-object))
  (equal (basic-object-value lhs) (basic-object-value rhs)))

;;; sexpr : should be a (possibly nested) list of string literals
(defun untype-everything (sexpr)
  (tree-map #'(lambda (string) (mk-untyped string)) sexpr))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; default fail transformer
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmethod inform ((object basic-object)
                   (transformer-name symbol)
                   (whoami symbol))
  (error "object with value {~A} doesn't implement 'inform' on ~A"
         (basic-object-value object) transformer-name))

(defmethod pass ((object basic-object)
                 (transformer-name symbol)
                 (args list))
  (error "object with value {~A} doesn't implement 'pass' on ~A"
         (basic-object-value object) transformer-name))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;    noop transformer
;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

(defmethod inform ((object basic-object)
                   (transformer-name (eql 'noop))
                   (whoami (eql 'arg)))
  (cons nil object))

(defmethod inform ((object basic-object)
                   (transformer-name (eql 'noop))
                   (whoami (eql 'lead)))
  t)

(defmethod pass ((object basic-object)
                 (transformer-name (eql 'noop))
                 (args list))
  (cons nil (append (list object) args)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;     infrastructure
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun back-talk-arg (transformer expr)
  (declare (optimize debug))
  (assert (typep expr 'atom))
  ;; response : (transform-more? . sexpr)
  (let ((response (inform expr (transformer-name transformer) 'arg)))
    (if (car response)
        (transform transformer (cdr response))
        (cdr response))))

(defun back-talk-sexpr (transformer lead &key expr-args)
  (declare (optimize debug))
  (assert (typep expr-args 'list))
  ;; response : can-i-talk-to-your-arguments?
  (let* ((response (inform lead (transformer-name transformer) 'lead))
         (args (mapcar #'(lambda (a)
                           (if response
                               (transform transformer a)
                               (identity a)))
                       expr-args)))
      ;; response : (transform-more? . sexpr)
      (let ((response-2 (pass lead (transformer-name transformer) args)))
        (if (car response-2)
            (transform transformer (cdr response-2))
            (cdr response-2)))))

;;; transform a single expression {sexpression, atom}
(defun transform (transformer expr)
  (cond ((atom expr) (back-talk-arg transformer expr))
        ((null expr) '())
        (t
          (back-talk-sexpr transformer (car expr) :expr-args (cdr expr)))))

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
    (and (equal (tokenize-parenlist next-char-fn)
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
         (char= (funcall next-char-fn 'peak) #\))
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
    (eq-tree (transform noop-transformer untyped-expr) untyped-expr
             :test #'eq-object)))

