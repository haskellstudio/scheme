#lang nanopass

(require nanopass/base)

(define-language Lsrc
  (terminals
   (int64 (n))
   (boolean (b))
   (symbol (x)))
  (Expr (e)
        n x b
        (= e1 e2)
        (+ e1 e2)
        (if e1 e2 e3)
        (cond [e1 e2] ... [e3])
        (when e1 e2)
        (λ (x) e)
        (e1 e2))
  (entry Expr))


(define (int64? x)
  (and (integer? x)
       (<= (- (expt 2 63)) x (- (expt 2 63) 1))))

;(language->s-expression Lsrc)


;(with-output-language (Lsrc Expr) `5)

;(define (add a b)
  ;(+ a b))

(define-language L1
  (extends Lsrc)
  (Expr (e)
        (- (when e1 e2))))


;(language->s-expression L1)


(define-pass desugar-when : Lsrc (e) -> L1 ()
  (Expr : Expr (e) -> Expr ()
        [(when ,[e1] ,[e2])
         `(if ,e1 ,e2 #f)]))


;(with-output-language (Lsrc Expr)
  ;(desugar-when `(+ 5 (when #t 6))))
    



(define-language L2
  (extends L1)
  (Expr (e)
        (- (cond [e1 e2] ... [e3]))))


(define-pass desugar-cond : L1 (e) -> L2 ()
  (Expr : Expr (e) -> Expr ()
        [(cond [,[e1]])
         e1]
        [(cond [,[e1] ,[e1*]] [,e2 ,e2*]  ...  [,e3])
         `(if ,e1  ,e1*  ,(with-output-language (L1 Expr)
                            (Expr `(cond [,e2 ,e2*] ... [,e3]))))]))



;(with-output-language (L1 Expr)
;     (desugar-cond `(cond [(= 5 6) 7]
;                          [(= 8 9) 10]
;                          [42])))



(define-language L3
  (extends L2)
  (Expr (e)
        (- (λ (x) e))
        (+ (λ (x) fe)))
  (FreeVars-Expr (fe)
                 (+ (free (x ...) e))))


(define-pass identify-free-variables : L2 (e) -> L3 ()
  (Expr : Expr (e) -> Expr ('())
       ; [,x (values x (list x))]
        [(+ ,[e1 a1] ,[e2 a2])
         (values `(+ ,e1 ,e2)
                 (set-union a1 a2))]
        #||# [(= ,[e1 a1] ,[e2 a2])
         (values `(= ,e1 ,e2)
                 (set-union a1 a2))]
        [(if ,[e1 a1] ,[e2 a2] ,[e3 a3])
         (values `(if ,e1 ,e2,e3)
                 (set-union a1 a2 a3))]
       [(λ (,x) ,[e1 a1])
         (define a* (set-remove a1 x))
         (values `(λ (,x) (free (,a* ...) ,e1))
                 a*)]
        [(,[e1 a1] ,[e2 a2])
         (values `(,e1 ,e2)
                 (set-union a1 a2))]   )
  (let-values ([(res free) (Expr e)])
    (unless (set-empty? free)
      (error 'compiler "Unbound variables: ~a" free))
    res))
#|
(with-output-language (L2 Expr)
    (identify-free-variables
     `(λ (x)
        (+ x x))))

(with-output-language (L2 Expr)
    (identify-free-variables
     `(+ 1 1)))


[(λ (,x) ,[e1 a1])     ; e1 is the first identify-free-variables return value
                       ; a1 is the second identify-free-variables  return value
 (define a* (set-remove a1 x))  ; remove x from a1 
 (values `(λ (,x) (free (,a* ...) ,e1))  ; a* is the free variable. (some context)  this line is first return value, just the code.
         a*)]                            ; a* is the second return value , is the free variable list . 


|#



