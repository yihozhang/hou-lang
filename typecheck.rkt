#lang typed/racket

(provide (all-defined-out))

(define-type Id Symbol)

(define-type Bindings (Listof (List Id Expr)))

(struct Forall ([xs : (Listof Id)] [ts : (Listof Expr)] [e : Expr]) #:transparent)
(struct Exists ([xs : Id] [t : Expr] [e : Expr]) #:transparent)
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
   'Bot
   
   'U
   ; term
   ; nat 
   (List 'succ Expr)
   'zero
   (List 'refl Expr Expr)
   (List 'ind-= Expr Expr Expr Expr Expr Expr Expr)
   (List 'intro-ex Expr Expr Expr Expr)
   (List 'elim-ex Expr Expr)
   (List 'exfalso Expr Expr)
   (List 'ind-Nat Expr Expr Expr Expr)
   (List 'the Expr Expr)
   ; var
   Id
   (Pairof Expr (Listof Expr))
   ))

(define-type Context (Listof (List Id Expr)))

(define debug? #f)

(: debugln (-> String Void))
(define (debugln s)
  (when debug? (displayln (string-append "DEBUG: " s))))

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
  (debugln (format "s: ~a\nx: ~a\n" s x))
  (let fresh* ([n 0])
    (let ([x+ (string->symbol (string-append (symbol->string x) (number->string n)))])
      (if (set-member? s x+)
          (fresh* (add1 n))
          x+))))

; TODO: implement computation rule for ind-Nat
(: normalize (-> Expr Expr))
(define (normalize e)
  (match e
    [(Forall xs ts e1) (Forall xs (map normalize ts) (normalize e1))]
    [(Exists x t e1) (Exists x (normalize t) (normalize e1))]
    [(Lambda xs e1) (Lambda xs (normalize e1))]
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
         [`(elim-ex ,A ,P (intro-ex ,A* ,P* ,x ,Px) ,B ,f)
          #:when (and (α-equiv A '() A* '())
                      (α-equiv P '() P* '()))
          (normalize `(,f ,x ,Px))]
         [`(ind-Nat zero ,motive ,base ,step) base]
         [`(ind-Nat (succ ,n) ,motive ,base ,step) (normalize `(,step ,n (ind-Nat ,n ,motive ,base ,step)))]
         [`(the ,A ,a) a]
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
    [(Exists x t e1)
     (set-union (set-subtract (free-vars e1) (set x))
                (free-vars t))]
    [(Lambda xs e1) (set-subtract (free-vars e1) (apply set xs))]
    ['refl (set)]
    ['= (set)]
    ['Nat (set)]
    ['U (set)]
    ['Bot (set)]
    ['ind-= (set)]
    ['ind-Nat (set)]
    ['intro-ex (set)]
    ['elim-ex (set)]
    ['succ (set)]
    ['exfalso (set)]
    ['zero (set)]
    ['the (set)]
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

(: subst (-> Id Expr Expr Expr))
(define (subst x v e)
  (substs `((,x ,v)) e))

(: substs (-> Context Expr Expr))
(define (substs xvs e)
  (define (subst1 [e : Expr]) : Expr (substs xvs e))
  (define (subst-qualifier [ys : (Listof Id)]
                           [ts : (Listof Expr)]
                           [e : Expr]) : (Values (Listof Id) (Listof Expr) Expr)
    ; Okay so this is really dumb, it first calculates the substitutions that will
    ; happen on the subexpression e (filter out shadowed ones)
    (define ys-set (apply set ys))
    (define tot-ts ts)
    (let self ([xvs xvs]
               [ys ys]
               [ts ts]
               [e e])
      (match (list ys ts)
        [(list '() '()) (values '() '() (substs xvs e))]
        [(list (cons y ys+) (cons t ts+))
         (define t+ (substs xvs t))
         (define fv-t+ (free-vars t+))
         (define xvs+ (filter (λ ([xv : (List Id Expr)]) (not (equal? (first xv) y))) xvs))
         (define vs (map (λ ([xv : (List Id Expr)]) (second xv)) xvs+))
         ; TODO: optimizations here since fv-vs is calculated for every parameter in a call
         (define fv-vs (free-vars+ vs))
         (if (set-member? fv-vs y)
             ; if v's may be captured by y do α-renaming
             (let* ([fv (set-union fv-vs ; free vars of v's
                                   fv-t+ ; free vars of t's
                                   ys-set ; all y's
                                   (free-vars e) ; free vars of new e
                                   )]
                    [y+ (fresh fv y)]
                    [ts++ (map (λ ([t : Expr]) (subst y y+ t)) ts+)]
                    [e+ (subst y y+ e)])
               (let-values ([(ys ts e++) (self xvs+ ys+ ts++ e+)])
                 (values (cons y+ ys) (cons t+ ts) e++)))
             (let-values ([(ys ts e++) (self xvs+ ys+ ts+ e)])
               (values (cons y ys) (cons t+ ts) e++)))])))
    
;    ; new types after substitution
;    (define ts+ : (Listof Expr)
;      (map (λ ([t : Expr]) (substs xvs t)) ts))
;    (define fv-ts+ : (Setof Id)
;      (free-vars+ ts+))
;    ; new (id, exp) pair, filter out symbols that are not free occurrence in e
;    (define xvs+ : Context
;      (filter (λ ([xv : (List Id Expr)]) (not (member (first xv) ys)))
;              xvs))
;    (define vs (map (λ ([xv : (List Id Expr)]) (second xv)) xvs+))
;    (define fv-vs : (Setof Id) (free-vars+ vs))
;    (define ys-set (apply set ys))
;    
;    (match-define (list #{ys+ : (Listof Id)} #{e+ : Expr})
;      (foldl (λ ([y : Id] [datum : (List (Listof Id) Expr)]) : (List (Listof Id) Expr)
;               (match-define (list old-ys e) datum)
;               (if (set-member? fv-vs y)
;                   ; if v's may be captured by y do α-renaming
;                   (let* ([fv (set-union fv-vs ; free vars of v's
;                                         fv-ts+ ; free vars of t's
;                                         ys-set ; all y's
;                                         (free-vars e) ; free vars of new e
;                                         (apply set old-ys) ; all updated old-ys
;                                         )]
;                          [y+ (fresh fv y)]
;                          [e+ (substs (list (list y y+)) e)])
;                     (list (append old-ys (list y+)) e+))
;                   (list (append old-ys (list y)) e)))
;             (list '() e) ys))
;    (values ys+ ts+ (substs xvs+ e+)))
  (match e
    [(Forall ys ts e)
     (let-values ([(ys+ ts+ e+) (subst-qualifier ys ts e)])
       (Forall ys+ ts+ e+))]
    [(Exists y t e)
     (let-values ([(y+ t+ e+) (subst-qualifier (list y) (list t) e)])
       (Exists (car y+) (car t+) e+))]
    [(Lambda ys e)
     (let-values ([(ys+ _ e+) (subst-qualifier ys (map (λ (_) 'Bot) ys) e)]) ; Bot is dummy type
       (Lambda ys+ e+))]
    ['= '=]
    ['ind-= 'ind-=]
    ['ind-Nat 'ind-Nat]
    ['intro-ex 'intro-ex]
    ['elim-ex 'elim-ex]
    ['Nat 'Nat]
    ['U 'U]
    ['Bot 'Bot]
    ['the 'the]
    ['exfalso 'exfalso]
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
           (second
            (foldl (λ ([tv : Expr] [tw : Expr] [res : (List Integer Boolean)])
                     : (List Integer Boolean)
                     (if (and (second res)
                              (α-equiv-imp tv (append (reverse (take xvs (first res))) lv)
                                           tw (append (reverse (take xws (first res))) lw)))
                         (list (add1 (first res)) #t)
                         (list 0 #f)))
                   (list 0 #t)
                   tvs tws))
           (α-equiv-imp ev (append (reverse xvs) lv)
                        ew (append (reverse xws) lw))))
    (match `(,v ,w)
      [(list (Forall xvs tvs ev) (Forall xws tws ew))
       (α-equiv-qualifier xvs tvs ev xws tws ew)]
      [(list (Exists xv tv ev) (Exists xw tw ew))
       (α-equiv-qualifier (list xv) (list tv) ev (list xw) (list tw) ew)]
      [(list (Lambda xvs ev) (Lambda xws ew))
       (α-equiv-qualifier xvs '() ev xws '() ew)]
      ['(= =) #t]
      ['(Bot Bot) #t]
      ['(exfalso exfalso) #t]
      ['(ind-= ind-=) #t]
      ['(ind-Nat ind-Nat) #t]
      ['(Nat Nat) #t]
      ['(U U) #t]
      ['(intro-ex intro-ex) #t]
      ['(elim-ex elim-ex) #t]
      ['(the the) #t]
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
  (debugln (format "inferring ~a under ~a" e Γ))
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
    [(Exists x t e) (infer-qualifier (list x) (list t) e)]
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
    ['ind-Nat (define args : Context
                `([n Nat]
                  [motive ,(Forall '(n) '(Nat) 'U)]
                  [base (motive zero)]
                  [step ,(Forall '(n IH) '(Nat (motive n)) '(motive (succ n)))]))
              (define-values (xs ts) (split-context args))
              (Forall xs ts '(motive n))]
    ['intro-ex (define args : Context
                 `([A U]
                   [P ,(Forall '(x) '(A) 'U)]
                   [x A]
                   [Px (P x)]))
               (define-values (xs ts) (split-context args))
               (Forall xs ts (Exists 'x 'A '(P x)))]
    ['elim-ex (define args : Context
                `([A U]
                  [P ,(Forall '(x) '(A) 'U)]
                  [base ,(Exists 'y 'A '(P y))]
                  [B U]
                  [f ,(Forall '(x e) '(A (P x)) 'B)]))
              (define-values (xs ts) (split-context args))
              (Forall xs ts 'B)]
    ['the (Forall '(A a) '(U A) 'A)]
    ['exfalso (Forall '(bot A) '(Bot U) 'A)]
    ['Bot 'U]
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
  (debugln (format "checking ~a under ~a against type ~a" e Γ t))
  (define t+ (normalize t))
  (match e
    [(Lambda ys e) (match t+
                     ; TODO: maybe some alpha-renaming is needed here...
                     [(Forall xs ts t) (check (add-to-context Γ ys ts) e (substs+ xs ys t))]
                     [_ #f])]
    [e (mlet* ([inferred-t (infer Γ e)])
              (debugln (format "inferred-type for ~a under ~a is ~a" e Γ inferred-t))
              (debugln (format "expected type is ~a" t+))
              (α-equiv t+ Γ inferred-t Γ))]))

(define-type Ast (U Symbol (Listof Ast)))

(: Ast->Expr (-> Ast Expr))
(define (Ast->Expr ast)
  (match ast
    [`(forall ([,(? symbol? #{xs : (Listof Symbol)}) ,#{ts : (Listof Ast)}] ...) ,e)
     (if (null? xs)
         (Ast->Expr e)
         (Forall xs (map Ast->Expr ts) (Ast->Expr e)))]
    [`(exists ([,(? symbol? #{xs : (Listof Symbol)}) ,#{ts : (Listof Ast)}] ...) ,e)
     (let self ([xs xs]
                [ts ts])
       (if (null? xs)
           (Ast->Expr e)
           (Exists (car xs) (Ast->Expr (car ts)) (self (cdr xs) (cdr ts)))))]
    [`(,(or 'lambda 'λ) (,(? symbol? #{xs : (Listof Symbol)}) ...) ,e) (Lambda xs (Ast->Expr e))]
    [`(,#{rator : Ast} ,#{rands : (Listof Ast)} ...) (cons (Ast->Expr rator) (map Ast->Expr rands))]
    ['⊥ 'Bot]
    [(? symbol? x) x]))
