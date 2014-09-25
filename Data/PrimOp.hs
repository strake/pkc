module Data.PrimOp where

data PrimOp = PrimNeg
            | PrimEq | PrimNEq
            | PrimGEq | PrimLEq
            | PrimGÞ | PrimLÞ
            | PrimAnd | PrimOr | PrimXor
            | PrimShiftL | PrimRotL
            | PrimShiftR | PrimRotR
            | PrimAdd | PrimSub | PrimMul | PrimDiv | PrimRem
            ;
