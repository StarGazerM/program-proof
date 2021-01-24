;; some note on classical logic 

#lang racket


(define (found? a) (not (equal? a '∅)))

;; formula predicates
(define (formula? f)
  (match f
    ['⊥ #t]
    ['⊤ #t]
    [(? symbol?) #t]
    #;[`(VAR ,(? symbol?)) #t]
    [`(∧ ,(? formula?) ,(? formula?)) #t]
    [`(∨ ,(? formula?) ,(? formula?)) #t]
    [`(⇒ ,(? formula?) ,(? formula?)) #t]
    [`(¬ ,(? formula?)) #t]
    [_ #f]))

;; test grammar
(define lf1
  '(⇒ (∨ A B)
      (¬ (∧ (¬ A)
             (¬ B)))))

;; a literal is either a var or a neg var
(define (literal? l)
  (match l
    ['⊤ #f]
    ['⊥ #f]
    [`(¬ ⊤) #f]
    [`(¬ ⊥) #f]
    [`(¬ ,(? symbol?)) #t]
    [(? symbol?) #t]
    [_ #f]))

;; clause is a disjunction of literal
(define (clause? c)
  (match c
    ['⊥ #t]
    [(? literal?) #t]
    [`(∨ ,(? clause?) ...) #t]
    [_ #f]))

;; conjunctive normal form
(define (clausal-form? cnf)
  (match cnf
    ['⊤ #t]
    [(? clause?) #t]
    [`(∧ ,(? clausal-form?) ...) #t]
    [_ #f]))

;; putting a form into cnf
;; a naive try just appy deMorgan rule, this is inefficient and may not terminate
;; for simplicity assume all logic operator is binary here
#;(define/contract (formula->cnf f)
  (-> formula? clausal-form?)
  ;;(pretty-display f)
  (define next-step
    (match f
      [`(¬ (∧ ,(? formula? a) ,(? formula? b)))
       `(∨ (¬ ,(formula->cnf a)) (¬ ,(formula->cnf b)))]
      [`(¬ (∨ ,(? formula? a) ,(? formula? b)))
       `(∧ (¬ ,(formula->cnf a)) (¬ ,(formula->cnf b)))]
      [`(∨ (∧ ,(? formula? a) ,(? formula? b))
           ,(? formula? c))
       (define cnf-a (formula->cnf a))
       (define cnf-b (formula->cnf b))
       (define cnf-c (formula->cnf c))
       `(∧ (∨ ,cnf-a ,cnf-c)
           (∨ ,cnf-b ,cnf-c))]
      [`(∨ ,(? formula? a)
           (∧ ,(? formula? b)) ,(? formula? c))
       (define cnf-a (formula->cnf a))
       (define cnf-b (formula->cnf b))
       (define cnf-c (formula->cnf c))
       `(∧ (∨ ,cnf-a ,cnf-b)
           (∨ ,cnf-a ,cnf-c))]
      [`(⇒ ,(? formula? a) ,(? formula? b))
       `(∨ (¬ ,(formula->cnf a))
           ,(formula->cnf b))]
      [`(¬ ⊥)  '⊤]
      [`(¬ ⊤) '⊥]
      [`(∨ ⊤ ,(? formula?)) '⊤]
      [`(∨ ,(? formula?) ⊤) '⊤]
      [`(¬ (¬ ,(? formula? a)))
       (formula->cnf a)]
      [(? clausal-form?) f]
      [`(∨ ,a ,b) `(∨ ,(formula->cnf a) ,(formula->cnf b))]
      [`(∧ ,a ,b) `(∧ ,(formula->cnf a) ,(formula->cnf b))]
      [`(¬ ,a) `(¬ ,(formula->cnf a))]))
  (if (clausal-form? next-step)
      next-step
      (formula->cnf next-step)))

(define example2552
  '(⇒ (⇒ X Y)
      (⇒ Y Z)))


;; efficient way of compute cnf

;; get set of literal inside a formula

(define (get-lit f)
  (match f
    ['⊤ '()]
    ['⊥ '()]
    [(? literal?) `(,f)]
    [`(∨ ,as ...) (foldl (λ (x res) (set-union res (get-lit x))) '() as)]
    [`(∧ ,as ...) (foldl (λ (x res) (set-union res (get-lit x))) '() as)]
    [`(¬ ,a) (get-lit a)]))

;; during computation in algorithm, a clause will be represent
;; by all literal inside it, and then a cnf become a set of set
;; var encode into {⊤,X}/{⊥,X}

(define/contract (formula->cnf f)
  (-> formula? clausal-form?)
  ;; merge 2 clause form A ∨ B(cartesian-product)
  #;(define (merge a b) (apply append (cartesian-product a b)))
  (define (merge a b)
    (apply append (map (λ (c)
                         (map (λ (d)
                                (append c d))
                              b))
                       a)))
  (define (pos pf)
    (match pf
      ['⊤ '()]
      ['⊥ '(())]
      [(? symbol?) `((,pf))]
      [`(∧ ,a ,b)
       (append (pos a) (pos b))]
      [`(∨ ,a ,b)
       (merge (pos a) (pos b))]
      [`(⇒ ,a ,b)
       (merge (neg a) (pos b))]
      [`(¬ ,a) (neg a)]))
  (define (neg nf)
    (match nf
      ['⊤ '(())]
      ['⊥ '()]
      [(? symbol?) `(((¬ ,nf)))]
      [`(∧ ,a ,b) (merge (neg a) (neg b))]
      [`(∨ ,a ,b) (append (neg a) (neg b))]
      [`(⇒ ,a ,b) (append (pos a) (neg b))]
      [`(¬ ,a) (pos a)]
))
  (define (decode l)
    (cond
      [(empty? l) '⊤]
      ['(()) '⊥]
      [(equal? (length l) 1) (car l)]
      [(list? l)
       `(∧ ,@(map (λ (c)
                    (if (empty? c)
                        '⊥
                        `(∨ ,@(remove-duplicates c))))
                  l))]))
  (if (clausal-form? f)
      f
      (decode (pos f))))

;; encode a cnf into list of list
(define (encode cnf)
  (match cnf
    ['⊤ '()]
    ['⊥ '(())]
    [(? literal? a) `(,a)]
    [`(∧ ,cs ...)
     (map (λ (c)
            (match c
              ['⊥ '()]
              [(? literal? a) `(, a)]
              [`(∨ ,ls ...) ls]))
          cs)]))

;;;;;;;;;;;;;;;;;;;; boolean satisfiable ;;;;;;;;;;;;;;;;;;;;;;;

;; substitute a variable by a formula in a formula
(define (subst x c f)
  (match f
    ['⊤ '⊤]
    ['⊥ '⊥]
    [(? symbol? y)
     (if (equal? x y) c y)]
    [`(∧ ,as ...)
     `(∧ ,@(map (λ (a) (subst x c a)) as))]
    [`(∨ ,as ...)
     `(∨ ,@(map (λ (a) (subst x c a)) as))]
    [`(¬ ,a) `(¬ ,(subst x c a))]))

;; find **one** free variable inside a formula
;; if not found return '∅
(define (find-one-freevar f)
  #;(displayln f)
  (match f
    ['⊤ '∅]
    ['⊥ '∅]
    [(? symbol? x) x]
    [`(∧ ,cs ...)
     (let/ec ret
       (foldl (λ (c res)
                (let ([fv (find-one-freevar c)])
                  (if (found? fv)
                      (ret fv)
                      res)))
              '∅
              cs))]
    [`(∨ ,cs ...)
     (let/ec ret
       (foldl (λ (c res)
                (let ([fv (find-one-freevar c)])
                  (if (found? fv)
                      (ret fv)
                      res)))
              '∅
              cs))]
    [`(¬ ,a) (find-one-freevar a)]))

;; eval a closed formula
(define (eval-close f)
  #;(displayln f)
  (match f
    ['⊤ #t]
    ['⊥ #f]
    [(? symbol?) (error "this function is only for closed formula")]
    [`(∧ ,cs ...) (foldl (λ (c res) (and res (eval-close c))) #t cs)]
    [`(∨ ,cs ...) (foldl (λ (c res) (or res (eval-close c))) #f cs)]
    [`(¬ ,a) (not (eval-close a))]))

;; a naive way of compute satisfibility
(define (sat-naive a)
  (define x (find-one-freevar a))
  (if (found? x)
      (or (sat-naive (subst x '⊤ a))
          (sat-naive (subst x '⊥ a)))
      (eval-close a)))

;; find a unitary clause
;; unitary is a clause contain only a literal
(define (find-one-unit f)
  (match f
    [`(∧ ,cs ...)
     (let/ec ret
       (foldl (λ (c res) (if (literal? c)
                         (ret c)
                         res))
              '∅
              cs))]
    ['⊤ '∅]))

;; find a pure literal in a cnf
;; pure var is a variable contain only one polarity
(define (find-one-pure f)
  (define lits (get-lit f))
  (let/ec ret
    (foldl (λ (l res)
             (match l
               [(? symbol? x)
                (if (member `(¬ ,x) lits)
                    res
                    (ret l))]
               [`(¬ ,x)
                (if (member x lits)
                    res
                    (ret l))]))
           '∅
           lits)))


;; using dpll to check satisfibility
(define (sat-dpll cnf)
  #;(define cnf (formula->cnf f))
  #; (define cnf-l (encode cnf))
  (cond
    [(equal? '⊤ cnf) #t]
    [(equal? '⊥ cnf) #f]
    [(member '⊥ cnf) #f]
    [(found? (find-one-unit cnf))
     (define found (find-one-unit cnf))
     #;(displayln found)
     (match found
       [(? symbol? x) (sat-dpll (subst x '⊤ cnf))]
       [`(¬ ,x) (sat-dpll (subst x '⊥ cnf))])]
    [(found? (find-one-pure cnf))
     (define found (find-one-pure cnf))
     (displayln found)
     (match found
       [(? symbol? x) (sat-dpll (subst x '⊤ cnf))]
       [`(¬ ,x) (sat-dpll (subst x '⊥ cnf))])]
    [else (sat-naive cnf)]))

(define example0
  '(∧ (∨ (¬ n) (¬ t))
      (∨ m q n)
      (∨ l (¬ m))
      (∨ l (¬ q))
      (∨ (¬ l) (¬ p))
      (∨ r p n)
      (∨ (¬ r) (¬ l))
      t))

(define example1
  '(∧ (∨ p q r)
      (∨ p q (¬ r))
      (∨ p (¬ q) r)
      (∨ p (¬ q) (¬ r))
      (∨ (¬ p) q r)
      (∨ (¬ p) q (¬ r))
      (∨ (¬ p) (¬ q) r)))

#;(sat-dpll example1)
