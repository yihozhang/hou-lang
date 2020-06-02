#lang typed/racket

(define-type Id Symbol)

(define-type Bindings (Listof (List Id Expr)))

(struct Forall ([xs : (Listof Id)] [ts : (Listof Expr)] [e : Expr]) #:transparent)
(struct Exists ([xs : (Listof Id)] [ts : (Listof Expr)] [e : Expr]) #:transparent)
(struct Lambda ([xs : (Listof Id)] [e : Expr]) #:transparent)

(define-type  Expr
  (U
   ; type
   Forall
   Exists
   Lambda
   ; (List '= Expr Expr Expr)
   '=
   'Nat
   
   'U
   ; term
   ; nat 
   'succ
   'zero
   'refl
   'ind-=
   ; var
   Id
   (Pairof Expr (Listof Expr))
   ))

(define-type Context (Listof (List Id Expr)))

(: lookup (-> Context Id (Option Expr)))
(define (lookup Γ x)
  (match Γ
    [`((,x+ ,e) ,#{Γ+ : Context} ...)
     (if (eq? x x+)
         e
         (lookup Γ+ x))]
    ['() #f]))
(: index-of (All (a) (-> (Listof a) a  Integer)))
(define (index-of lst v)
  (: inner (All (a) (-> (Listof a) a Integer Integer)))
  (define (inner lst v idx)
    (match lst
      [(cons x xs) (if (equal? x v) idx (inner xs v (add1 idx)))]
      ['() (error (format "~a not found" v))]))
  (inner lst v 0))

(define-syntax mlet*
  (syntax-rules ()
    [(mlet* ([x e] [x+ e+] ...) s ...)
     (let ([x e])
       (if x
           (mlet* ([x+ e+] ...) s ...)
           #f))]
    [(mlet* () s ...)
     (begin s ...)]))

(: fresh (-> (Setof Id) Id Id))
(define (fresh s x)
  (let fresh* ([n 0])
    (let ([x+ (string->symbol (string-append (symbol->string x) (number->string n)))])
      (if (set-member? s x+)
          (fresh* (add1 n))
          x+))))
   

(: normalize (-> Expr Expr))
(define (normalize e)
  (match e
    [(Forall xs ts e1) (Forall xs (map normalize ts) (normalize e1))]
    [(Exists xs ts e1) (Exists xs (map normalize ts) (normalize e1))]
    [(Lambda xs e1) (Lambda xs (normalize e1))]
    ['= '=]
    ['Nat 'Nat]
    ['U 'U]
    ['ind-= 'ind-=]
    ['refl 'refl]
    ['succ 'succ]
    ['zero 'zero]
    [`(,#{rator : Expr} ,#{rands : (Listof Expr)} ...)
     (let ([rator+ : Expr (normalize rator)]
           [rands+ : (Listof Expr) (map normalize rands)])
       (match `(,rator+ ,@rands+)
         [`(,(Lambda xs e) ,#{rands+ : (Listof Expr)} ...)
          (if (= (length xs) (length rands+))
              (normalize (substs+ xs rands+ e))
              (error "arity does not match"))]
         [`(ind-= ,A ,fr ,to (refl ,A* ,fr*) ,motive ,base)
          #:when (and (α-equiv fr '() to '())
                      (α-equiv fr '() fr* '())
                      (α-equiv A '() A* '()))
          base]
         [_ (ann `(,rator+ ,@rands+) Expr)]))]
    [x #:when (symbol? x) x]
    [_ (error (format "NORMALIZE ERROR: unrecognizable type ~a" e))]))

(: free-vars (-> Expr (Setof Id)))
(define (free-vars e)
  (match e
    [(Forall xs ts e1)
     (apply set-union
            ; remove all xs from free variables of e1
            (set-subtract (free-vars e1) (apply set xs))
            (map free-vars ts))]
    [(Exists xs ts e1)
     (apply set-union
            ; remove all xs from free variables of e1
            (set-subtract (free-vars e1) (apply set xs))
            (map free-vars ts))]
    [(Lambda xs e1) (set-subtract (free-vars e1) (apply set xs))]
    ['refl (set)]
    ['= (set)]
    ['Nat (set)]
    ['U (set)]
    ['ind-= (set)]
    ['succ (set)]
    ['zero (set)]
    [`(,rator ,#{rand : (Listof Expr)} ...) (apply set-union (free-vars rator) (map free-vars rand))]
    [x #:when (symbol? x) (set x)]))

(: free-vars+ (-> (Listof Expr) (Setof Id)))
(define (free-vars+ es)
  (foldl (λ ([e : Expr] [s : (Setof Id)]) (set-union s (free-vars e)))
         (ann (set) (Setof Id)) es))

(: substs+ (-> (Listof Id) (Listof Expr) Expr Expr))
(define (substs+ xs vs e)
  (let ([xvs (map (λ ([x : Id] [v : Expr]) (list x v)) xs vs)])
    (substs xvs e)))

(: substs (-> Context Expr Expr))
(define (substs xvs e)
  (define (subst1 [e : Expr]) : Expr (substs xvs e))
  (define (subst-qualifier [ys : (Listof Id)]
                           [ts : (Listof Expr)]
                           [e : Expr]) : (Values (Listof Id) (Listof Expr) Expr)
    ; new types after substitution
    (define ts+ : (Listof Expr)
      (map (λ ([t : Expr]) (substs xvs t)) ts))
    (define fv-ts+ : (Setof Id)
      (free-vars+ ts+))
    ; new (id, exp) pair, filter out symbols that are not free occurrence in e
    (define xvs+ : Context
      (filter (λ ([xv : (List Id Expr)]) (not (member (first xv) ys)))
              xvs))
    (define vs (map (λ ([xv : (List Id Expr)]) (second xv)) xvs+))
    (define fv-vs : (Setof Id) (free-vars+ vs))
    (define ys-set (apply set ys))
    
    (match-define (list #{ys+ : (Listof Id)} #{e+ : Expr})
      (foldl (λ ([y : Id] [datum : (List (Listof Id) Expr)]) : (List (Listof Id) Expr)
               (match-define (list old-ys e) datum)
               (if (set-member? fv-vs y)
                   ; if v's may be captured by y do α-renaming
                   (let* ([fv (set-union fv-vs ; free vars of v's
                                         fv-ts+ ; free vars of t's
                                         ys-set ; all y's
                                         (free-vars e) ; free vars of new e
                                         (apply set old-ys) ; all updated old-ys
                                         )]
                          [y+ (fresh fv y)]
                          [e+ (substs (list (list y y+)) e)])
                     (list (cons y+ old-ys) e+))
                   (list (cons y old-ys) e)))
             (list '() e) ys))
    (values ys+ ts+ (substs xvs+ e+)))
  (match e
    [(Forall ys ts e)
     (let-values ([(ys+ ts+ e+) (subst-qualifier ys ts e)])
       (Forall ys+ ts+ e+))]
    [(Exists ys ts e)
     (let-values ([(ys+ ts+ e+) (subst-qualifier ys ts e)])
       (Exists ys+ ts+ e+))]
    [(Lambda ys e)
     (let-values ([(ys+ _ e+) (subst-qualifier ys '() e)])
       (Lambda ys+ e+))]
    ['= '=]
    ['ind-= 'ind-=]
    ['Nat 'Nat]
    ['U 'U]
    ['refl 'refl]
    ['zero 'zero]
    ['succ 'succ]
    [`(,#{rator : Expr} ,#{rands : (Listof Expr)} ...) `(,(subst1 rator) ,@(map subst1 rands))]
    [x #:when (symbol? x) (or (lookup xvs x) x)]
    [_ (error (format "NORMALIZE ERROR: unrecognizable type ~a" e))]))

(: add-to-context (-> Context (Listof Id) (Listof Expr) Context))
(define (add-to-context Γ xs vs)
  (append (reverse (map (λ ([x : Id] [v : Expr]) (list x v)) xs vs))
          Γ))

(define (split-context [args : Context]) : (Values (Listof Id) (Listof Expr))
  (match args
    [`((,a ,b) ,#{args : Context} ...)
     (let-values ([(as bs) (split-context args)])
       (values (cons a as) (cons b bs)))]
    ['() (values '() '())]))

; input to α-equiv should be a value
(: α-equiv (-> Expr Context Expr Context Boolean))
(define (α-equiv v Γv w Γw)
  (: α-equiv-imp (-> Expr (Listof Id) Expr (Listof Id) Boolean))
  (define (α-equiv-imp v lv w lw)
    (: α-equiv-qualifier (-> (Listof Id) (Listof Expr) Expr
                             (Listof Id) (Listof Expr) Expr
                             Boolean))
    (define (α-equiv-qualifier xvs tvs ev xws tws ew)
      (and (= (length xvs) (length xws))
           (= (length tvs) (length tws))
           (andmap (λ ([tv : Expr] [tw : Expr]) (α-equiv-imp tv lv tw lw)) tvs tws)
           (α-equiv-imp ev (append (reverse xvs) lv)
                        ew (append (reverse xws) lw))))
    (match `(,v ,w)
      [(list (Forall xvs tvs ev) (Forall xws tws ew))
       (α-equiv-qualifier xvs tvs ev xws tws ew)]
      [(list (Exists xvs tvs ev) (Exists xws tws ew))
       (α-equiv-qualifier xvs tvs ev xws tws ew)]
      [(list (Lambda xvs ev) (Lambda xws ew))
       (α-equiv-qualifier xvs '() ev xws '() ew)]
      ['(= =) #t]
      ['(ind-= ind-=) #t]
      ['(Nat Nat) #t]
      ['(U U) #t]
      ['(zero zero) #t]
      ['(succ succ) #t]
      ['(refl refl) #t]
      [(list (list #{ratorv : Expr} #{randvs : (Listof Expr)} ...)
             (list #{ratorw : Expr} #{randws : (Listof Expr)} ...))
       (and (= (length randvs) (length randws))
            (α-equiv-imp ratorv lv ratorw lw)
            (andmap (λ ([v : Expr] [w : Expr]) (α-equiv-imp v lv w lw)) randvs randws))]
      [(list (? symbol? x) (? symbol? y)) (= (index-of lv x) (index-of lw y))]
      ;[_ #f]
      ))
  (define first* (ann first (-> (List Id Expr) Id)))
  (α-equiv-imp v (map first* Γv) w (map first* Γw)))

; return type will be a value
(: infer (-> Context Expr (Option Expr)))
(define (infer Γ e)
  ; (printf "LOG: inferring ~a under ~a\n" e Γ)
  (define (infer-qualifier [xs : (Listof Id)] [ts : (Listof Expr)] [e : Expr]) : (Option 'U)
    (define (process [Γ : Context]
                     [xs : (Listof Id)]
                     [ts : (Listof Expr)]) : (Values Context Boolean)
      (match (list xs ts)
        [(list (list) (list)) (values Γ #t)]
        [(list (list x xs ...) (list t ts ...))
         (if (check Γ t 'U)
             (process (add-to-context Γ (list x) (list (normalize t)))
                      xs ts)
             (values '() #f))]))
    (define-values (Γ+ res) (process Γ xs ts))
    (if (and res (check Γ+ e 'U)) 'U #f))
  (match e
    [(Forall xs ts e) (infer-qualifier xs ts e)]
    [(Exists xs ts e) (infer-qualifier xs ts e)]
    ['= (Forall '(t lhs rhs) '(U t t) 'U)]
    ['ind-= (define args : Context
              `([A U]
                [fr A]
                [to A]
                [target (= A fr to)]
                [motive ,(Forall '(x evidence)
                                 '(A (= A fr x))
                                 'U)]
                [base (motive fr (refl A fr))]))
            (define-values (xs ts) (split-context args))
            (Forall xs ts '(motive to target))]
    ['Nat 'U]
    ['U 'U]
    [`(,#{rator : Expr} ,#{rands : (Listof Expr)} ...)
     (mlet* ([rator-ty (infer Γ rator)])
            (match rator-ty
              [(Forall xs ts e) (mlet* ([_ (= (length xs) (length rands))]
                                        [res (foldl (λ ([rand : Expr] [t : Expr] [datum : (List (Listof Expr) Boolean)]) : (List (Listof Expr) Boolean)
                                                      (match-define `(,old-rands ,b) datum)
                                                      ;(displayln (format "datum ~a" datum))
                                                      (if b (let* ([len (length old-rands)]
                                                                   [old-xs (take xs len)]
                                                                   [t+ (substs+ old-xs old-rands t)])
                                                              (list (append old-rands (list rand)) (check Γ rand t+)))
                                                          (list (append old-rands (list rand)) #f)))
                                                    (list '() #t) rands ts)]
                                        [_ (second res)])
                                       (normalize (substs+ xs rands e)))]
              [_ (begin
                   (printf "operator ~a is not of forall type, but ~a\n" rator rator-ty)
                   #f)]))]
    ;    [`(succ ,n) (mlet* ([_ (check Γ n 'Nat)])
    ;                       'Nat)]
    ['refl (Forall '(T x) '(U T) '(= T x x))]
    ['succ (Forall '(n) '(Nat) 'Nat)]
    ['zero 'Nat]
    [(? symbol? x) (lookup Γ x)]
    [_ (begin
         (printf "can't infer type of ~a under ~a\n" e Γ)
         #f)]))
    
; t should be normalized
(: check (-> Context Expr Expr Boolean))
(define (check Γ e t)
  ; (printf "LOG: checking ~a under ~a against type ~a\n" e Γ t)
  (define t+ (normalize t))
  (match e
    [(Lambda ys e) (match t+
                     ; TODO: maybe some alpha-renaming is needed here...
                     [(Forall xs ts t) (check (add-to-context Γ ys ts) e (substs+ xs ys t))]
                     [_ #f])]
    [e (mlet* ([inferred-t (infer Γ e)])
              ; (printf "LOG: inferred-type for ~a under ~a is ~a\n" e Γ inferred-t)
              (α-equiv t+ Γ inferred-t Γ))]))

(define-type Ast (U Symbol (Listof Ast)))

(: Ast->Expr (-> Ast Expr))
(define (Ast->Expr ast)
  (match ast
    [`(forall ([,(? symbol? #{xs : (Listof Symbol)}) ,#{ts : (Listof Ast)}] ...) ,e) (Forall xs (map Ast->Expr ts) (Ast->Expr e))]
    [`(exists ([,(? symbol? #{xs : (Listof Symbol)}) ,#{ts : (Listof Ast)}] ...) ,e) (Exists xs (map Ast->Expr ts) (Ast->Expr e))]
    [`(,(or 'lambda 'λ) (,(? symbol? #{xs : (Listof Symbol)}) ...) ,e) (Lambda xs (Ast->Expr e))]
    [`(,#{rator : Ast} ,#{rands : (Listof Ast)} ...) (cons (Ast->Expr rator) (map Ast->Expr rands))]
    [(? symbol? x) x]))

(define symm-ty : Expr
  (Ast->Expr '(forall ([A U]
                       [n A]
                       [m A]
                       [eq (= A n m)])
                      (= A m n))))
(define symm-tm : Expr
  (Ast->Expr '(lambda (A n m eq)
                (ind-= A n m
                       eq
                       (lambda (x eq) (= A x n))
                       (refl A n)))))

(define trans-ty : Expr
  (Ast->Expr '(forall ([A U]
                       [x A]
                       [y A]
                       [z A]
                       [x=y (= A x y)]
                       [y=z (= A y z)])
                      [= A x z])))

(define trans-tm : Expr
  (Ast->Expr '(λ (A x y z x=y y=z)
                (ind-= A y x
                       (symm-ty A x y x=y)
                       (λ (w x=w) (= A w z))
                       y=z))))
(time
 (assert (check '() symm-ty 'U))
 (assert (check '() symm-tm symm-ty))
 (assert (check '() trans-ty 'U))
 (assert (check `((symm-ty ,symm-ty)) trans-tm trans-ty)))