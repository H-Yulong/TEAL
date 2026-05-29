module Main where

-- General helper functions
import Basic

-- Simple types, context, variables, renamings
import Context

{-

===================================================
  Functional: SECD machine with code on the stack 
===================================================

-}

-- Untyped syntax of the SECD machine: 
-- instructions, operational semantics, structural properties
import Functional.Syntax

{- Term language: STLC -}

-- Intrinsic encoding of STLC using datatypes (deep embedding)
import Functional.Calculus.Syntax

-- Shallow embedding of STLC (makes checking definitional equality trivial)
import Functional.Calculus.Shallow

{- Type machine: Γ ⊢ ins : Δ ⟶ Δ' -}

-- Extrinsic typing rules, proofs of properties: 
-- progress, preservation
import Functional.TypeMachine.Types

-- Proof of termination
import Functional.TypeMachine.Termination

-- Intrinsic syntax, ompilation from STLC
-- The intrinsic syntax makes it easy to write programs 
-- and let Agda figure the types out.
-- See more in the examples
import Functional.TypeMachine.Intrinsic

{- Term machine: Γ ⊢ ins : σ ⟶ σ' -}

-- Extrinsic typing rules, proofs of properties:
-- progress, preservation, termination, total correctness
import Functional.TermMachine.Types

-- Intrinsic syntax, compilation from STLC
import Functional.TermMachine.Intrinsic

{- Examples -}
import Functional.Example
