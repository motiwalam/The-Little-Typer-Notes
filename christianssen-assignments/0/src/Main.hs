module Main where


data Expr = CstI Integer
          | Bin BinOp Expr Expr
          | Un UnOp Expr
  deriving Show


data BinOp = Plus | Times | Minus | Div
  deriving Show

data UnOp = Neg
  deriving Show

type Value = Integer

type ErrorMessage = String

failure :: String -> Either ErrorMessage a
failure message = Left message


eval :: Expr -> Either ErrorMessage Value
eval (CstI n) =
  return n
eval (Bin op e1 e2) =
  do v1 <- eval e1
     v2 <- eval e2
     doBin op v1 v2
eval (Un op e) =
  do v <- eval e
     doUn op v

doBin :: BinOp -> Value -> Value -> Either ErrorMessage Value
doBin Plus i j = return (i + j)
doBin Minus i j = return (i - j)
doBin Times i j = return (i * j)
doBin Div i j =
  if j == 0
    then failure "Division by zero"
    else return (div i j)

doUn :: UnOp -> Value -> Either ErrorMessage Value
doUn Neg i = return (- i)

main :: IO ()
main = putStrLn "Hello Haskell!"
