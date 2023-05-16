module Main where

-- Here is a bidirectional type checker for simply-typed λ-calculus
-- with added natural numbers. Your task is to enrich it with more
-- types.
--
-- Task 0: Write down the rules that correspond to the existing code.
--
--   If you do this on paper, please submit a JPEG or PNG or PDF with
--   a scan or legible photo. If you do it digitally (e.g. with
--   LaTeX), please submit a PDF. Text files are also acceptable.
--
--   The rule names are in comments that begin with "Rule".
--
-- Task 1: Add a type called Trivial, with a single constructor sole.
-- This type is the unit type, corresponding to () in Haskell.
--
--  (a) First add a constructor to Ty for Trivial and to Expr for
--      sole.  Here, the only thing that needs to be the case for a
--      thing to be a valid type is that it can be represented by the
--      datatype Ty, so there's no need to code this rule:
--
--      ------------------
--       Γ ⊢ Trivial type
--
--  (b) Next get the type checker to recognize these new constructors,
--  with the following rules:
--
--    ----------------------------- [Trivial≡]
--      Γ ⊢ Trivial ≡ Trivial type
--
--    -------------------------- [TrivialI]
--      Γ ⊢ sole ⇐ Trivial
--
--  (c) Implement enough tests to be convinced of the correctness of
--  your code.
--
-- Task 2: Add a pair type.
--
--  (a) First extend Ty with a new constructor for Pair, and extend
--  Expr with constructors for cons, car, and cdr.
--
--  (b) Extend the type checker to support the following rules:
--
--    Γ ⊢ A1 ≡ A2 type    Γ ⊢ D1 ≡ D2 type
--  --------------------------------------- [Pair≡]
--    Γ ⊢ (Pair A1 D1) ≡ (Pair A2 D2) type
--
--    Γ ⊢ p ⇒ (Pair A D)
--   -------------------- [PairE1]
--     Γ ⊢ (car p) ⇒ A
--
--    Γ ⊢ p ⇒ (Pair A D)
--   -------------------- [PairE2]
--     Γ ⊢ (cdr p) ⇒ D
--
--    Γ ⊢ a ⇐ A        Γ ⊢ d ⇐ D
--   ------------------------------ [PairI]
--     Γ ⊢ (cons a d) ⇐ (Pair A D)
--
--  (c) Implement enough tests to be convinced of the correctness of
--  your code.
--
-- Task 3:
--   In a comment or in a separate text file, answer the following:
--
--     Which of the checking rules in this assignment could be
--     synthesis rules instead? Hint: try to write the corresponding
--     type checker program.
--


newtype Name = Name String
  deriving (Eq, Show)

newtype Message = Message String
  deriving Show

newtype Context = Context [(Name, Ty)]

initCtx :: Context
initCtx = Context []

data Ty = Nat | Arr Ty Ty
  deriving (Eq, Show)

data Expr = The Ty Expr
          | Var Name
          | Lambda Name Expr
          | App Expr Expr
          | Zero
          | Add1 Expr
          | Rec Ty Expr Expr Expr
  deriving Show

failure :: String -> Either Message a
failure message = Left (Message message)

lookupVarTy (Context []) x = failure ("Variable not found: " ++ show x)
lookupVarTy (Context ((y, t) : ctx)) x
  | x == y    = return t
  | otherwise = lookupVarTy (Context ctx) x

extend :: Context -> Name -> Ty -> Context
extend (Context ctx) x t = Context ((x, t) : ctx)

sameType :: Ty -> Ty -> Either Message ()
sameType Nat Nat = return () -- Rule: Nat≡
sameType (Arr a1 b1) (Arr a2 b2) = -- Rule: →≡
  do sameType a2 a1
     sameType b1 b2
sameType t1 t2 =
  failure ("Not the same type: " ++ show t1 ++ " " ++ show t2)

check :: Context -> Expr -> Ty -> Either Message ()
check ctx (Lambda x body) t = -- Rule: →I
  case t of
    Arr a b ->
      check (extend ctx x a) body b
    other -> failure ("Not a function type: " ++ show other)
check ctx Zero t = -- Rule: NatI1
  case t of
    Nat -> return ()
    other -> failure ("Not Nat: " ++ show other)
check ctx (Add1 n) t = -- Rule: NatI2
  case t of
    Nat -> check ctx n Nat
    other -> failure ("Not Nat: " ++ show other)
check ctx other t = -- Rule: Switch
  do t' <- synth ctx other
     sameType t' t

synth :: Context -> Expr -> Either Message Ty
synth ctx (The t e) = -- Rule: The
  do check ctx e t
     return t
synth ctx (Var x) = -- Rule: Var
  lookupVarTy ctx x
synth ctx (App rator rand) = -- Rule: →E
  do ratorT <- synth ctx rator
     case ratorT of
       Arr a b ->
         do check ctx rand a
            return b
       other ->
         failure ("Not a function type: " ++ show other)
synth ctx (Rec t tgt base step) = -- Rule: NatE
  do check ctx tgt t
     check ctx base t
     check ctx step (Arr Nat (Arr t t))
     return t
synth ctx other =
  failure ("Can't synthesize a type for " ++ show other)

------------------------------------------------------------------------
-- Test code begins here

shouldSynth :: String -> Expr -> Ty -> IO ()
shouldSynth name e t =
  do putStr (name ++ ": ")
     case synth initCtx e of
       Left (Message err) -> error err
       Right t'
         | t' == t -> putStrLn "Success"
         | otherwise -> putStrLn "Failure"

main :: IO ()
main =
  do shouldSynth
       "Nat identity"
       (The (Arr Nat Nat) (Lambda (Name "x") (Var (Name "x"))))
       (Arr Nat Nat)
     shouldSynth
       "+"
       (The (Arr Nat (Arr Nat Nat))
            (Lambda (Name "j")
              (Lambda (Name "k")
                (Rec Nat
                  (Var (Name "j"))
                  (Var (Name "k"))
                  (Lambda (Name "j-1")
                    (Lambda (Name "sum")
                      (Add1 (Var (Name "sum")))))))))
       (Arr Nat (Arr Nat Nat))
     shouldSynth
       "five"
       (App
        (App
         (The (Arr Nat (Arr Nat Nat))
            (Lambda (Name "j")
              (Lambda (Name "k")
                (Rec Nat
                  (Var (Name "j"))
                  (Var (Name "k"))
                  (Lambda (Name "j-1")
                    (Lambda (Name "sum")
                      (Add1 (Var (Name "sum")))))))))
          (Add1 (Add1 (Add1 Zero))))
         (Add1 (Add1 Zero)))
       Nat



