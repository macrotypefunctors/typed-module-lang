#lang s-exp typed-module-lang/core-lang

(type Color = Int)
(val black : Color = 0)
(val white : Color = 100)
(val mix : (-> Color Color Color) =
  (λ (c1 c2) (quo (+ c1 c2) 2)))

(type Image = (-> Int Int Color))
(val mix-image : (-> Image Image Image) =
  (λ (i1 i2)
    (λ (x y)
      (mix (i1 x y) (i2 x y)))))

(check (mix white black) = 50)
