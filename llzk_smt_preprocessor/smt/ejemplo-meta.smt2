(define-fun main ((v_0 FFp) (v_4 FFp) (v_1 FFp) (v_2 FFp) (v_3 FFp)) Bool
  (and
    (and
      (!
        (ite
          (= v_0 1)
          (!
            (= v_1 (ff.mul v_0 1))
          :meta-data "%z := felt.mul %x 1")
          (!
            (foo v_0 v_1 v_2)
          :meta-data "call foo (%x) to %z")
        )
      :meta-data "if (%x == 1)")
      (!
        (= v_3 (ff.add v_1 1))
      :meta-data "%y := felt.add %z 1")
    )
    (= v_4 v_3)
  )
)
