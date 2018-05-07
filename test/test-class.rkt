#lang s-exp typed-module-lang/core-lang

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

#;
(instance (Condition Int)
  [test = (λ ([x : Int]) (if (= x 0) #f #t))])

#;
(instance (Condition A) => (Condition (-> A))
  [test = (Λ (A)
            (=> (Condition A)
              (λ ([f : (-> A)])
                ((inst test A) (f)))))])
