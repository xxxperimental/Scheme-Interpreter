(load "./chez-init.ss")

(define-datatype expression expression?
  [lit-exp (value always?)]
  [var-exp (id symbol?)]
  [app-exp (rator expression?) (rands (list-of expression?))]
  [set!-exp (target symbol?) (val expression?)]
  [if1-exp (condition expression?) (arm1 expression?)]
  [if2-exp (condition expression?) (arm1 expression?) (arm2 expression?)]
  [lambda-exp (vars list?) (bodies (list-of expression?))]
  [lambdai-exp (vars pair?) (bodies (list-of expression?))]
  [lambdal-exp (var symbol?) (bodies (list-of expression?))]
  [let-exp (varnames list?) (varexps list?) (bodies (list-of expression?))]
  [letn-exp (id symbol?) (varnames list?) (varexps list?) (bodies (list-of expression?))]
  [let*-exp (varnames list?) (varexps list?) (bodies (list-of expression?))]
  [letr-exp (proc-names (list-of symbol?)) (varnames pair?) (varexps pair?) (bodies (list-of expression?))]
  [begin-exp (bodies (list-of expression?))]
  [cond-exp (conditions (list-of expression?)) (bodies (list-of expression?))]
  [cond-else-exp (conditions (list-of expression?)) (bodies (list-of expression?)) (else-body expression?)]
  [and-exp (conditions (list-of expression?))]
  [or-exp (conditions (list-of expression?))]
  [case-exp (test-val expression?)
            (conditions (list-of (list-of (lambda (x) (or (symbol? x) (number? x))))))
            (bodies (list-of expression?))]
  [case-else-exp (test-val expression?)
                 (conditions (list-of (list-of (lambda (x) (or (symbol? x) (number? x))))))
                 (bodies (list-of expression?)) (else-body expression?)]
  [while-exp (condition expression?) (bodies (list-of expression?))]
  [define-exp (id symbol?) (val expression?)])

(define-datatype environment environment?
  [empty-env-record]
  [extended-env-record
   (syms (list-of symbol?))
   (vals (list-of scheme-value?))
   (env environment?)]
  [recursively-extended-env-record
   (proc-names (list-of symbol?))
   (idss list?)
   (bodiess (list-of (list-of expression?)))
   (env environment?)])

(define-datatype proc-val proc-val?
  [prim-proc
   (name symbol?)]
  [closure
    (vars (list-of symbol?))
    (bodies (list-of expression?))
    (env environment?)]
  [improper-closure
    (vars (lambda (ls) (andmap-improper symbol? ls))) ; equivalent-ish to improper-list-of symbol?
    (bodies (list-of expression?))
    (env environment?)]
  [list-closure
    (var-list symbol?)
    (bodies (list-of expression?))
    (env environment?)]
  [kont-proc
    (kont kontinuation?)])

(define-datatype kontinuation kontinuation?
  [init-k]
  [if1-k (arm1 expression?) (env environment?) (k kontinuation?)]
  [if2-k (arm1 expression?) (arm2 expression?) (env environment?) (k kontinuation?)]
  [rator-k (rands (list-of expression?)) (env environment?) (k kontinuation?)]
  [rands-k (proc-value proc-val?) (k kontinuation?)]
  [map-proc-k (map-cdr (list-of scheme-value?)) (proc-cps procedure?) (k kontinuation?)]
  [map-k (proc-res scheme-value?) (k kontinuation?)]
  [eval-bodies-k (bodies-cdr (list-of expression?)) (env environment?) (k kontinuation?)]
  [set-exp-k (env environment?) (target symbol?) (k kontinuation?)]
  [eval-exp-k (exp expression?) (env environment?) (k kontinuation?)]
  [define-k (id symbol?) (syms (list-of symbol?)) (vals (list-of scheme-value?)) (env environment?) (k kontinuation?)])

(define-datatype cell cell?
  [cell-record
    (value box?)])

(define apply-k
  (lambda (k v)
    (cases kontinuation k
      [init-k ()
        v]
        ;(pretty-print v)]
        ;(rep)]
      [if1-k (arm1 env k)
        (if v
          (eval-exp-cps arm1 env k)
          (apply-k k (void)))]
      [if2-k (arm1 arm2 env k)
        (if v
          (eval-exp-cps arm1 env k)
          (eval-exp-cps arm2 env k))]
      [rator-k (rands env k)
        (eval-rands-cps rands env (rands-k v k))]
      [rands-k (proc-value k)
        (apply-proc-cps proc-value v k)]
      [map-proc-k (map-cdr proc-cps k)
        (map-cps proc-cps map-cdr (map-k v k))]
      [map-k (proc-res k)
        (apply-k k (cons proc-res v))]
      [eval-bodies-k (bodies-cdr env k)
        (eval-bodies-cps bodies-cdr env k)]
      [set-exp-k (env target k)
        (apply-k k (set-ref!
                    (apply-env-ref env target
                      (lambda (x) x)
                      (lambda () (apply-env-ref global-env target
                                                (lambda (x) x)
                                                (lambda () (eopl:error 'apply-env
                                                                "variable not found in environment: ~s" target)))))
                    v))]
      [eval-exp-k (exp env k)
        (eval-exp-cps exp env k)]
      [define-k (id syms vals env k)
        (apply-k k (set! global-env (extended-env-record (cons id syms) (cons (make-cell v) vals) env)))])))
      ;[extend-env-k (varnames varexps env k)
        ;(let ([extended-env
                ;(extend-env varnames (map (lambda (varexp) (eval-exp varexp env)) varexps) env)]))])))

(define let-exp-arg-vals
  (lambda (let-exp)
    (map (lambda (x) (parse-exp (cadr x))) let-exp)))

(define let-exp-args
  (lambda (let-exp)
    (map (lambda (x) (parse-exp (car x))) let-exp)))

(define quoted-list?
  (lambda (x)
    (and (pair? x) (eqv? (car x) 'quote) (list? (cadr x)) (null? (cddr x)))))

(define quoted-vector?
  (lambda (x)
    (and (pair? x) (eqv? (car x) 'quote) (vector? (cadr x)) (null? (cddr x)))))

(define quoted-symbol?
  (lambda (x)
    (and (pair? x) (eqv? (car x) 'quote) (symbol? (cadr x)) (null? (cddr x)))))

(define andmap-improper
  (lambda (pred impls)
    (if (pair? (cdr impls))
      (if (pred (car impls))
        (andmap-improper pred (cdr impls))
        #f)
      (not (not (and (pred (car impls)) (pred (cdr impls))))))))

(define parse-exp
  (lambda (datum)
    (cond [(symbol? datum) (var-exp datum)]
          [(or (number? datum) (vector? datum) (string? datum) (boolean? datum)) (lit-exp datum)]
          [(or (quoted-list? datum) (quoted-vector? datum) (quoted-symbol? datum))
            (lit-exp (cadr datum))]
          [(pair? datum)
           (cond [(eqv? (car datum) 'lambda)
                  (if (>= (length datum) 3)
                      (cond
                       [(list? (cadr datum))
                        (if (andmap symbol? (cadr datum))
                            (lambda-exp (cadr datum) (map parse-exp (cddr datum)))
                            (eopl:error 'parse-exp "Arguments must be symbols in a lambda expression."))]
                       [(and (pair? (cadr datum)) (not (list? (cadr datum))))
                        (if (andmap-improper symbol? (cadr datum))
                            (lambdai-exp (cadr datum) (map parse-exp (cddr datum)))
                            (eopl:error 'parse-exp "Arguments must be symbols in a lambda expression."))]
                       [else
                        (if (symbol? (cadr datum))
                            (lambdal-exp (cadr datum) (map parse-exp (cddr datum)))
                            (eopl:error 'parse-exp "Argument must be a symbol in a lambda expression."))])
                      (eopl:error 'parse-exp "Incorrect number of parameters for lambda expression, expected 3."))]
                 [(eqv? (car datum) 'if)
                  (if (and (<= (length datum) 4) (>= (length datum) 3))
                      (if (null? (cdddr datum))
                          (if1-exp (parse-exp (cadr datum))
                                   (parse-exp (caddr datum)))
                          (if2-exp (parse-exp (cadr datum))
                                   (parse-exp (caddr datum))
                                   (parse-exp (cadddr datum))))
                      (eopl:error 'parse-exp "Incorrect length of if expression"))]               
                 [(eqv? (car datum) 'let)
                  (if (>= (length datum) 3)
                      (if (symbol? (cadr datum))
                          (if (list? (caddr datum))
                              (if (and (andmap (lambda (x)
                                                 (and (list? x)
                                                      (equal? (length x) 2)))
                                               (caddr datum))
                                       (andmap symbol? (map car (caddr datum))))
                                  (letn-exp (cadr datum) (map car (caddr datum))
                                            (let-exp-arg-vals (caddr datum))
                                            (map parse-exp (cdddr datum)))
                                  (eopl:error 'parse-exp "Named let's list variables are not symbols"))
                              (eopl:error 'parse-exp "List of arguments is not a proper list"))
                          (if (list? (cadr datum))
                              (if (and (andmap (lambda (x)
                                                 (and (list? x)
                                                      (equal? (length x) 2)))
                                               (cadr datum))
                                       (andmap symbol? (map car (cadr datum))))
                                  (let-exp (map car (cadr datum))
                                           (let-exp-arg-vals (cadr datum))
                                           (map parse-exp (cddr datum)))
                                  (eopl:error 'parse-exp "Let's list variables are not symbols"))
                              (eopl:error 'parse-exp "List of arguments is not a proper list")))
                      (eopl:error 'parse-exp "Incorrect number of parameters for let expression"))]
                 [(eqv? (car datum) 'let*)
                  (if (>= (length datum) 3)
                      (if (list? (cadr datum))
                          (if (and (andmap (lambda (x)
                                             (and (list? x)
                                                  (equal? (length x) 2)))
                                           (cadr datum))
                                   (andmap symbol? (map car (cadr datum))))
                              (let*-exp (map car (cadr datum))
                                        (let-exp-arg-vals (cadr datum))
                                        (map parse-exp (cddr datum)))
                              (eopl:error 'parse-exp "Let*'s list variables are not symbols"))
                          (eopl:error 'parse-exp "List of arguments is not a proper list"))
                      (eopl:error 'parse-exp "Incorrect number of parameters for let* expression"))]
                 [(eqv? (car datum) 'letrec)
                  (if (>= (length datum) 3)
                      (if (list? (cadr datum))
                          (if (and (andmap (lambda (x)
                                             (and (list? x)
                                                  (equal? (length x) 2)))
                                           (cadr datum))
                                   (andmap symbol? (map car (cadr datum))))
                              (letr-exp (map car (cadr datum))
                                        (map cadadr (cadr datum))
                                        (map (lambda (x) (map parse-exp x))
                                             (map (lambda (x) (cddr (cadr x))) (cadr datum)))
                                        (map parse-exp (cddr datum)))
                              (eopl:error 'parse-exp "Letrec's list variables are not symbols"))
                          (eopl:error 'parse-exp "List of arguments is not a proper list"))
                      (eopl:error 'parse-exp "Incorrect number of parameters for letrec expression"))]
                 [(eqv? (car datum) 'begin)
                  (begin-exp (map parse-exp (cdr datum)))]
                 [(eqv? (car datum) 'cond)
                  (if (member 'else (map car (cdr datum)))
                    (cond-else-exp (reverse (cdr (reverse (map parse-exp (map car (cdr datum))))))
                                    (reverse (cdr (reverse (map parse-exp (map cadr (cdr datum))))))
                                    (car (reverse (map parse-exp (map cadr (cdr datum))))))
                    (cond-exp (map parse-exp (map car (cdr datum))) (map parse-exp (map cadr (cdr datum)))))]
                 [(eqv? (car datum) 'and)
                  (and-exp (map parse-exp (cdr datum)))]
                 [(eqv? (car datum) 'or)
                  (or-exp (map parse-exp (cdr datum)))]
                 [(eqv? (car datum) 'while)
                  (while-exp (parse-exp (cadr datum)) (map parse-exp (cddr datum)))]
                 [(eqv? (car datum) 'case)
                  (if (member 'else (map car (cddr datum)))
                    (case-else-exp (parse-exp (cadr datum))
                                   (reverse (cdr (reverse (map car (cddr datum)))))
                                   (reverse (cdr (reverse (map parse-exp (map cadr (cddr datum))))))
                                   (car (reverse (map parse-exp (map cadr (cddr datum))))))
                    (case-exp (parse-exp (cadr datum))
                              (map car (cddr datum))
                              (map parse-exp (map cadr (cddr datum)))))]
                 [(eqv? (car datum) 'set!)
                  (if (= (length datum) 3)
                      (set!-exp (cadr datum) (parse-exp (caddr datum)))
                      (eopl:error 'parse-exp "Incorrect number of parameters for set! expression"))]
                 [(eqv? (car datum) 'define)
                  (if (= (length datum) 3)
                      (define-exp (cadr datum) (parse-exp (caddr datum)))
                      (eopl:error 'parse-exp "Incorrect number of parameters for define expression"))]
                 [else (if (not (list? datum))
                    (eopl:error 'parse-exp "applications must be proper lists: ~s" datum)
                    (app-exp (parse-exp (car datum))
                       (map parse-exp (cdr datum))))])]
          [else (eopl:error 'parse-exp "Bad expression: ~s" datum)])))

(define syntax-expand
  (lambda (exp)
    (cases expression exp
           [let-exp (varnames varexps bodies)
                    (app-exp (lambda-exp varnames (map syntax-expand bodies)) (map syntax-expand varexps))]
           [let*-exp (varnames varexps bodies)                      
                     (if (= 1 (length varnames))
                         (syntax-expand (let-exp (list (car varnames))
                                                 (list (car varexps))
                                                 bodies))
                         (syntax-expand (let-exp (list (car varnames))
                                                 (list (car varexps))
                                                 (list (let*-exp (cdr varnames) (cdr varexps) bodies)))))]
           [begin-exp (bodies)
                      (app-exp (lambda-exp '() (map syntax-expand bodies)) '())]
           [cond-exp (conditions bodies)
                     (if (= 1 (length conditions))
                         (syntax-expand (if1-exp (car conditions)
                                                 (car bodies)))
                         (syntax-expand (if2-exp (car conditions)
                                                 (car bodies)
                                                 (cond-exp (cdr conditions) (cdr bodies)))))]
           [cond-else-exp (conditions bodies else-body)
                          (if (null? conditions)
                              (syntax-expand else-body)
                              (syntax-expand
                               (if2-exp (car conditions)
                                        (car bodies)
                                        (cond-else-exp (cdr conditions) (cdr bodies) else-body))))]
           [and-exp (conditions)
                    (if (null? conditions)
                        (lit-exp #t)
                        (if (= 1 (length conditions))
                            (syntax-expand (car conditions))
                            (syntax-expand
                              (let ([condition (car conditions)])
                               (if2-exp condition
                                        (and-exp (cdr conditions))
                                        condition)))))]
           [or-exp (conditions)
                   (if (null? conditions)
                       (lit-exp #f)
                       (if (= 1 (length conditions))
                           (syntax-expand (car conditions))
                           (syntax-expand
                            (let ([sym (gensym)])
                              (let-exp (list sym) (list (car conditions))
                                (list
                                  (if2-exp (parse-exp sym)
                                           (parse-exp sym)
                                           (or-exp (cdr conditions)))))))))]
           [case-exp (test-val conditions bodies)
                     (if (= 1 (length conditions))
                         (syntax-expand (if1-exp (app-exp (var-exp 'member) (list test-val (lit-exp (car conditions))))
                                                 (car bodies)))
                         (syntax-expand (if2-exp (app-exp (var-exp 'member) (list test-val (lit-exp (car conditions))))
                                                 (car bodies)
                                                 (case-exp test-val (cdr conditions) (cdr bodies)))))]
           [case-else-exp (test-val conditions bodies else-body)
                          (if (null? conditions)
                              (syntax-expand else-body)
                              (syntax-expand
                               (if2-exp (app-exp (var-exp 'member) (list test-val (lit-exp (car conditions))))
                                        (car bodies)
                                        (case-else-exp test-val (cdr conditions) (cdr bodies) else-body))))]
           [letn-exp (id varnames varexps bodies)
            (syntax-expand (letr-exp (list id) (list varnames) (list bodies) (list (app-exp (var-exp id) varexps))))]

           ;; core forms below
           [lit-exp (value) exp]
           [var-exp (id) exp]
           [app-exp (rator rands) (app-exp (syntax-expand rator) (map syntax-expand rands))]
           [set!-exp (target val) exp]
           [if1-exp (condition arm1) (if1-exp (syntax-expand condition) (syntax-expand arm1))]
           [if2-exp (condition arm1 arm2) (if2-exp (syntax-expand condition) (syntax-expand arm1) (syntax-expand arm2))]
           [lambda-exp (vars bodies) (lambda-exp vars (map syntax-expand bodies))]
           [lambdai-exp (vars bodies) (lambdai-exp vars (map syntax-expand bodies))]
           [lambdal-exp (vars bodies) (lambdal-exp vars (map syntax-expand bodies))]
           [while-exp (condition bodies) (while-exp (syntax-expand condition) (map syntax-expand bodies))]
           [define-exp (id val) (define-exp id (syntax-expand val))]
           [letr-exp (proc-names varnames varexps bodies)
                     (letr-exp proc-names varnames (map (lambda (x) (map syntax-expand x)) varexps) (map syntax-expand bodies))])))

(define unparse-let-exp-args
  (lambda  (args vals)
    (map (lambda (x y) (list x y))
         (map (lambda (x) (unparse-exp x)) args)
         (map (lambda (x) (unparse-exp x)) vals))))

(define unparse-exp
  (lambda (exp)
    (cases expression exp
           [var-exp (id) id]
           [lit-exp (value) value]
           [app-exp (rator rands)
             (cons (unparse-exp rator)
               (map unparse-exp rands))]
           [lambda-exp
            (vars bodies)
            (append (list 'lambda vars)
                    (map unparse-exp bodies))]
           [lambdai-exp
            (vars bodies)
            (append (list 'lambda vars)
                    (unparse-exp bodies))]
           [lambdal-exp
            (var bodies)
            (append (list 'lambda var)
                    (unparse-exp bodies))]
           [if1-exp
            (condition arm1)
            (list 'if (unparse-exp condition)
                  (unparse-exp arm1))]
           [if2-exp
            (condition arm1 arm2)
            (list 'if (unparse-exp condition)
                  (unparse-exp arm1)
                  (unparse-exp arm2))]
           [let-exp
            (varnames varexps bodies)
            (append (list 'let (unparse-let-exp-args varnames varexps))
                    (map unparse-exp bodies))]
           [letn-exp
            (id varnames varexps bodies)
            (append (list 'let id (unparse-let-exp-args varnames varexps))
                    (map unparse-exp bodies))]
           [let*-exp
            (varnames varexps bodies)
            (append (list 'let* (unparse-let-exp-args varnames varexps))
                    (map unparse-exp bodies))]
           [letr-exp
            (varnames varexps bodies)
            (append (list 'letrec (unparse-let-exp-args varnames varexps))
                    (map unparse-exp bodies))]
           [set!-exp
            (target val)
            (list 'set! target (unparse-exp val))])))




(define scheme-value?
  (lambda (x) #t))

(define make-cell
  (lambda (x)
    (cell-record (box x))))

(define cell-ref
  (lambda (c)
    (cases cell c
      [cell-record (value)
        (unbox value)]
      [else
        (eopl:error 'cell-ref "Value ~s is not a cell" c)])))

(define deref cell-ref)

(define cell-set!
  (lambda (c val)
    (cases cell c
      [cell-record (value)
        (set-box! value val)]
      [else
        (eopl:error 'cell-set! "Value ~s is not a cell" c)])))

(define set-ref! cell-set!)

(define apply-env-ref
  (lambda (env sym succeed fail)
    (cases environment env       ;  succeed is applied if sym is found, otherwise 
      [empty-env-record ()       ;  fail is applied.
        (fail)]
      [extended-env-record
       (syms vals env)
       (let ([pos (list-find-position sym syms)])
         (if (number? pos)
             (succeed (list-ref vals pos))
             (apply-env-ref env sym succeed fail)))]
      [recursively-extended-env-record
       (proc-names idss bodiess old-env)
       (let ([pos (list-find-position sym proc-names)])
         (if (number? pos)
          (cond
            [(symbol? (list-ref idss pos))
              (make-cell (list-closure
                  idss
                  (list-ref bodiess pos)
                  env))]
            [(and (pair? (list-ref idss pos)) (not (list? (list-ref idss pos))))
              (make-cell (improper-closure
                  (list-ref idss pos)
                  (list-ref bodiess pos)
                  env))]
            [else
              (make-cell (closure (list-ref idss pos)
                (list-ref bodiess pos)
                env))])
           (apply-env-ref old-env sym succeed fail)))])))

(define extend-env
  (lambda (syms vals env)
    (extended-env-record syms (map make-cell vals) env)))

(define recur-extend-env
  (lambda (proc-names idss bodiess old-env)
    (recursively-extended-env-record
     proc-names idss bodiess old-env)))

(define list-find-position
  (lambda (sym los)
    (list-index (lambda (xsym) (eqv? sym xsym)) los)))

(define list-index
  (lambda (pred ls)
    (cond
     ((null? ls) #f)
     ((pred (car ls)) 0)
     (else (let ((list-index-r (list-index pred (cdr ls))))
	     (if (number? list-index-r)
		 (+ 1 list-index-r)
		 #f))))))

(define apply-env
  (lambda (env sym succeed fail) ; succeed and fail are "callback procedures, 
    (deref (apply-env-ref env sym succeed fail))))


(define eval-bodies-cps
  (lambda (bodies env k)
    (if (null? (cdr bodies))
        (eval-exp-cps (car bodies) env k)
        (eval-exp-cps (car bodies) env (eval-bodies-k (cdr bodies) env k)))))

(define eval-exp-cps
  (lambda (exp env k)
    (cases expression exp
      [lit-exp (datum) (apply-k k datum)]
      [var-exp (id)
               (apply-k k (apply-env env id; look up its value.
                            (lambda (x) x) ; procedure to call if it is in the environment 
                            (lambda ()
                              (apply-env-ref global-env id
                                         (lambda (x) x)
                                         (lambda () (eopl:error 'apply-env ; procedure to call if it is not in env
                                                                "variable not found in environment: ~s" id))))))]
      [app-exp (rator rands)
               (eval-exp-cps rator env
                  (rator-k rands env k))]
      [set!-exp (target val)
                (eval-exp-cps val env
                  (set-exp-k env target k))]
      [if1-exp (condition arm1)
               (eval-exp-cps condition env (if1-k arm1 env k))]
      [if2-exp (condition arm1 arm2)
               (eval-exp-cps condition env (if2-k arm1 arm2 env k))]
      [lambda-exp (vars bodies)
                  (apply-k k (closure vars bodies env))]
      [lambdai-exp (vars bodies)
                   (apply-k k (improper-closure vars bodies env))]
      [lambdal-exp (var-list bodies)
                   (apply-k k (list-closure var-list bodies env))]
      ;[let-exp (varnames varexps bodies)
               ;(map-cps eval-exp-cps varexp env (extend-env-k varnames varexps env k))
               ;(let ([extended-env
                      ;(extend-env varnames (map (lambda (varexp) (eval-exp varexp env)) varexps) env)])
                 ;(eval-bodies-cps bodies extended-env k))]
      [letr-exp (proc-names idss bodiess bodies)
                (let ([rec-extended-env
                       (recur-extend-env proc-names idss bodiess env)])
                  (eval-bodies-cps bodies rec-extended-env k))]
      [while-exp (condition bodies)
                 (eval-exp-cps condition env (if1-k (eval-bodies-k bodies env (eval-exp-k exp env k)) env k))]
      [define-exp (id val)
                  (cases environment global-env
                    [extended-env-record (syms vals env)
                      (eval-exp-cps val env (define-k id syms vals env k))]
                    [else
                      (eopl:error 'eval-exp-cps "Bad number of arguments in define clause ~s" exp)])]
      
      ;;these will be syntax expanded out and thus never evaluated
      [begin-exp (bodies) exp]
      [cond-exp (conditions bodies) exp]
      [cond-else-exp (conditions bodies else-body) exp]
      [and-exp (conditions) exp]
      [or-exp (conditions) exp]
      [case-exp (test-val conditions bodies) exp]
      [case-else-exp (test-val conditions bodies else-body) exp]
      [else (eopl:error 'eval-exp-cps "Bad abstract syntax: ~a" exp)])))

(define map-cps
  (lambda (proc-cps ls k)
    (if (null? ls)
      (apply-k k ls)
      (proc-cps (car ls)
                (map-proc-k (cdr ls) proc-cps k)))))

(define eval-rands-cps
  (lambda (rands env k)
    (map-cps (lambda (x k)
               (eval-exp-cps x env k)) rands k)))

(define apply-proc-cps
  (lambda (proc-value args k)
    (cases proc-val proc-value
      [prim-proc (op) (apply-prim-proc-cps op args k)]
      [closure (vars bodies env)
        (let ([extended-env (extend-env vars args env)])
          (eval-bodies-cps bodies extended-env k))]
      [improper-closure (vars bodies env)
        (let* ([binding-list
                (let loop ([var vars] [args args] [current-var '()] [current-args '()])
                  (cond
                    [(and (null? args) (pair? var))
                      (eopl:error 'apply-proc-cps "Incorrect argument list for ~s" proc-value)]
                    [(pair? var) (loop (cdr var) (cdr args) (cons (car var) current-var) (cons (car args) current-args))]
                    [else (list (reverse (cons var current-var)) (reverse (cons args current-args)))]))]
                [extended-env (extend-env (car binding-list) (cadr binding-list) env)])
          (eval-bodies-cps bodies extended-env k))]
      [list-closure (var-list bodies env)
        (let ([extended-env (extend-env (list var-list) (list args) env)])
          (eval-bodies-cps bodies extended-env k))]
      [kont-proc (kont) (apply-k kont (car args))]
      [else (eopl:error 'apply-proc-cps
                   "Attempt to apply bad procedure: ~s"
                    proc-value)])))


(define *prim-proc-names* '(+ - * / add1 sub1 cons = zero? not < > <= >= != car cdr list null? assq eq? equal? atom? length list->vector list? pair? procedure? vector->list vector make-vector vector-ref vector? number? symbol? set-car! set-cdr! vector-set! display newline caar cadr cdar cddr caaar caadr cadar caddr cdaar cdadr cddar cdddr apply map member quotient append list-tail eqv? exit-list call/cc))

(define empty-env
  (lambda ()
    (empty-env-record)))

(define init-env         ; for now, our initial global environment only contains 
  (lambda ()
    (extend-env            ; procedure names.  Recall that an environment associates
       *prim-proc-names*   ; a value (not an expression) with an identifier.
       (map prim-proc
                      *prim-proc-names*)
       (empty-env))))

(define global-env (init-env))

(define reset-global-env
  (lambda ()
    (set! global-env (init-env))))

(define top-level-eval
  (lambda (form)
    (eval-exp-cps form (empty-env) (init-k))))


(define apply-prim-proc-cps
  (lambda (prim-proc args k)
    (case prim-proc
      [(apply) (apply-proc-cps (car args) (cadr args) k)]
      [(map) (map-cps (lambda (x k) (apply-proc-cps (car args) (list x) k)) (cadr args) k)]
      [(exit-list) args]
      [(call/cc) (apply-proc-cps (car args) (list (kont-proc k)) k)]       
      [else
        (apply-k k (case prim-proc
                      [(+) (apply + args)]
                      [(-) (apply - args)]
                      [(*) (apply * args)]
                      [(/) (apply / args)]
                      [(add1) (apply add1 args)]
                      [(sub1) (apply sub1 args)]
                      [(cons) (apply cons args)]
                      [(=) (apply = args)]
                      [(zero?) (apply zero? args)]
                      [(not) (apply not args)]
                      [(<) (apply < args)]
                      [(>) (apply > args)]
                      [(<=) (apply <= args)]
                      [(>=) (apply >= args)]
                      [(!=) (apply != args)]
                      [(car) (apply car args)]
                      [(cdr) (apply cdr args)]
                      [(list) (apply list args)]
                      [(null?) (apply null? args)]
                      [(assq) (apply assq args)]
                      [(eq?) (apply eq? args)]
                      [(equal?) (apply equal? args)]
                      [(atom?) (apply atom? args)]
                      [(length) (apply length args)]
                      [(list->vector) (apply list->vector args)]
                      [(list?) (apply list? args)]
                      [(pair?) (apply pair? args)]
                      [(procedure?) (or (apply proc-val? args) (apply procedure? args))]
                      [(vector->list) (apply vector->list args)]
                      [(vector) (apply vector args)]
                      [(make-vector) (apply make-vector args)]
                      [(vector-ref) (apply vector-ref args)]
                      [(vector?) (apply vector? args)]
                      [(number?) (apply number? args)]
                      [(symbol?) (apply symbol? args)]
                      [(set-car!) (apply set-car! args)]
                      [(set-cdr!) (apply set-cdr! args)]
                      [(vector-set!) (apply vector-set! args)]
                      [(display) (apply display args)]
                      [(newline) (apply newline args)]
                      [(printf) (apply printf args)]
                      [(caar) (apply caar args)]
                      [(cadr) (apply cadr args)]
                      [(cdar) (apply cdar args)]
                      [(cddr) (apply cddr args)]
                      [(caaar) (apply caaar args)]
                      [(caadr) (apply caadr args)]
                      [(cadar) (apply cadar args)]
                      [(caddr) (apply caddr args)]
                      [(cdaar) (apply cdaar args)]
                      [(cdadr) (apply cdadr args)]
                      [(cddar) (apply cddar args)]
                      [(cdddr) (apply cdddr args)]
                      [(member) (apply member args)]
                      [(quotient) (apply quotient args)]
                      [(append) (apply append args)]
                      [(list-tail) (apply list-tail args)]
                      [(eqv?) (apply eqv? args)]
                      [else (error 'apply-prim-proc-cps 
                              "Bad primitive procedure name: ~s" 
                              prim-op)]))])))

(define rep
	(lambda ()
		(display "-->")
		(let ([answer (top-level-eval (parse-exp (read)))])
		(eopl:pretty-print answer)
	(rep))))

(define eval-one-exp
  (lambda (x) (top-level-eval (syntax-expand (parse-exp x)))))
