#lang s-exp typed-module-lang/core-lang

;; Do not call until the instances are set up
(val f : (-> Int) =
     (λ ()
       ((resolve (inst if* Bool Int))
        #t
        (λ () ((resolve (inst if* Int Int)) 0 (λ () 5) (λ () 6)))
        (λ () 7))))

(class (Condition B)
  [test : (-> B Bool)])

(val if* : (∀ (X Y)
             (=> (Condition X)
               (-> X (-> Y) (-> Y) Y))) =
  (Λ (X Y)
    (=> (Condition X)
      (λ ([cnd : X] [thn : (-> Y)] [els : (-> Y)])
        (if ((resolve (inst test X)) cnd)
            (thn)
            (els))))))

(instance (Condition Bool)
  [test = (λ ([x : Bool]) x)])

(check ((resolve (inst if* Bool Int))
        #t
        (λ () 5)
        (λ () 7))
       = 5)


(instance (Condition Int)
  [test = (λ ([x : Int]) (if (= x 0) #f #t))])

(check ((resolve (inst if* Bool Int))
        #t
        (λ () ((resolve (inst if* Int Int)) 0 (λ () 5) (λ () 6)))
        (λ () 7))
       = 6)

(check (f) = 6)

#;
(instance (Condition A) => (Condition (-> A))
  [test = (Λ (A)
            (=> (Condition A)
              (λ ([f : (-> A)])
                ((inst test A) (f)))))])
