{-# LANGUAGE GADTs #-}

--         ∞
-- fix f = ⊔ fⁱ ⊥
--        i=0
fix :: (a -> a) -> a
fix f = f (fix f) -- A kind of magic!

type Iden = String

type Σ = Iden -> Int

-- Alias por si escribir Σ les resulta complicado
type State = Σ

-- Función de actualización de estado
update :: Iden -> Int -> Σ -> Σ
update v n σ v' =
  if v == v'
    then n
    else σ v'

{- Para probar con eval: usen al principio eIniTest que no rompe nada si quieren
    saber cuánto termina valiendo una variable  -}

eInicial, eIniTest :: Σ
eInicial = \v -> undefined
eIniTest = \v -> 0

{- Ω ≈ Σ + Σ -}
data Ω
  = Normal Σ
  | Abort Σ
  | Out (Int, Ω)
  | In (Int -> Ω)

{- Notar:
   * Normal : Σ → Ω
   * Abort  : Σ → Ω
   -}

-- Alias por si escribir Ω les resulta complicado
type Omega = Ω

data Expr a where
  {- Expresiones enteras -}

  -- n
  Const :: Int                  -> Expr Int
  -- v
  Var   :: Iden                 -> Expr Int
  -- e + e'
  Plus  :: Expr Int -> Expr Int -> Expr Int
  -- e - e'
  Dif   :: Expr Int -> Expr Int -> Expr Int
  -- e * e'
  Times :: Expr Int -> Expr Int -> Expr Int
  -- e / e' (división entera)
  Div   :: Expr Int -> Expr Int -> Expr Int
  -- Si e' evalúa a 0, hagan lo que quieran.

  {- Expresiones booleanas -}

  -- e = e'
  Eq   :: Expr Int  -> Expr Int -> Expr Bool
  -- e /= e'
  Neq  :: Expr Int  -> Expr Int -> Expr Bool
  -- e < e'
  Less :: Expr Int  -> Expr Int -> Expr Bool
  -- b && b'
  And  :: Expr Bool -> Expr Bool -> Expr Bool
  -- b || b'
  Or   :: Expr Bool -> Expr Bool -> Expr Bool
  -- ¬b
  Not  :: Expr Bool              -> Expr Bool

  {- Comandos -}

  -- SKIP
  Skip   ::                                    Expr Ω
  -- NEWVAR v := e IN c
  Local  :: Iden      -> Expr Int -> Expr Ω -> Expr Ω
  -- v := e
  Assign :: Iden      -> Expr Int           -> Expr Ω
  -- FAIL
  Fail   ::                                    Expr Ω
  -- CATCHIN c WITH c'
  Catch  :: Expr Ω    -> Expr Ω             -> Expr Ω
  -- WHILE b DO c
  While  :: Expr Bool -> Expr Ω             -> Expr Ω
  -- IF b THEN c ELSE c'
  If     :: Expr Bool -> Expr Ω   -> Expr Ω -> Expr Ω
  -- c ; c'
  Seq    :: Expr Ω    -> Expr Ω             -> Expr Ω
  -- ?x
  Input :: Iden -> Expr Ω
  -- !x
  Output :: Expr Int -> Expr Ω


{- Completar las ecuaciones semánticas -}

class DomSem dom where
  sem :: Expr dom -> Σ -> dom

instance DomSem Int where
  sem (Const a) _    = a
  sem (Var v) σ      = σ v
  sem (Plus e1 e2) σ = sem e1 σ + sem e2 σ
  sem (Dif e1 e2) σ = sem e1 σ - sem e2 σ
  sem (Times e1 e2) σ = sem e1 σ * sem e2 σ
  sem (Div e1 e2) σ = if sem e2 σ == 0 then 0 else sem e1 σ `div`sem e2 σ

instance DomSem Bool where
  sem (Eq e1 e2) σ = sem e1 σ == sem e2 σ
  sem (Neq e1 e2) σ = sem e1 σ /= sem e2 σ
  sem (Less e1 e2) σ = sem e1 σ < sem e2 σ
  sem (And e1 e2) σ = sem e1 σ && sem e2 σ
  sem (Or e1 e2) σ = sem e1 σ || sem e2 σ
  sem (Not e1) σ = not (sem e1 σ)
  
{- Función de control para Ω -}

(*.) :: (Σ -> Ω) -> Ω -> Ω
(*.) f (Normal σ) = f σ
(*.) _ (Abort σ)  = Abort σ
(*.) f (In g) = In ((f *.).g)
(*.) f (Out (n, ω)) = Out (n, (f *. ω))

(+.) :: (Σ -> Ω) -> Ω -> Ω
(+.) _ (Normal σ) = Normal σ
(+.) f (Abort σ)  = f σ
(+.) f (In g) = In ((f +.).g)
(+.) f (Out (n, ω)) = Out (n, (f +. ω))

(†) :: (Σ -> Σ) -> Ω -> Ω
(†) f (Normal σ) = Normal (f σ)
(†) f (Abort σ) = Abort (f σ)
(†) f (In g) = In ((f †).g)
(†) f (Out (n, ω)) = Out (n, (f † ω))

instance DomSem Ω where
  sem Skip σ = Normal σ
  sem (Local v e c) σ = update v (σ v) † sem c (update v (sem e σ) σ)
  sem (Assign v e) σ = Normal (update v (sem e σ) σ)
  sem Fail σ = Abort σ
  sem (Catch c c') σ = (sem c') +. (sem c σ)
  sem (While b c) σ = fix f σ
    where
        f :: (Σ -> Ω) -> Σ -> Ω
        f g σ' | sem b σ' = g *. sem c σ'
               | otherwise = Normal σ'
  sem (If b c c') σ | sem b σ = sem c σ
                    | otherwise = sem c' σ
  sem (Seq c c') σ = (sem c') *. (sem c σ)
  sem (Output n) σ = Out (sem n σ, Normal σ)
  sem (Input v) σ = In (\n -> Normal (update v n σ))

{- ################# Funciones de evaluación de dom ################# -}
class Eval dom where
  eval :: Expr dom -> Σ -> IO ()

instance Eval Int where
  eval e = print . sem e

instance Eval Bool where
  eval e = print . sem e

instance Eval Ω where
  eval :: Expr Ω -> Σ -> IO ()
  eval e = unrollOmega . sem e
    where
      unrollOmega :: Ω -> IO ()
      unrollOmega (Normal σ) = return ()
      unrollOmega (Abort σ) = putStrLn "Abort"
      unrollOmega (Out (n, ω)) = print n >> unrollOmega ω
      unrollOmega (In f) = getLine >>= unrollOmega . f . read

-- Ejemplo

-- fact
ejemploFact :: Expr Ω
ejemploFact =
  Seq (Input "x") $
  If (Less (Var "x") (Const 0)) Fail $
  Seq (Assign "y" (Const 1)) $
  Seq (While (Neq (Var "x") (Const 0)) $
    Seq (Assign "y" (Times (Var "y") (Var "x"))) $
    Assign "x" (Dif (Var "x") (Const 1))
  ) $
  Output (Var "y")

ejecutarFact :: IO ()
ejecutarFact = eval ejemploFact eIniTest

-- divMod
progDivMod =
  Seq (Input "x") $
  Seq (Input "y") $
  Seq (If
    (Or
      (Or (Less (Var "y") (Const 0)) (Eq (Var "y") (Const 0)))
      (Less (Var "x") (Const 0))
    )
    Fail
    (Local "q" (Const 0)
      (Local "r" (Var "x")
        (Seq
          (Seq
            (While
              (Not (Less (Var "r") (Var "y")))
              (Seq
                (Assign "q" (Plus (Var "q") (Const 1)))
                (Assign "r" (Dif (Var "r") (Var "y")))
              )
            )
            (Assign "x" (Var "q"))
          )
          (Assign "y" (Var "r"))
        )
      )
    )) $
  Seq (Output (Var "x")) $
  Output (Var "y")

ejecutarDivMod :: IO ()
ejecutarDivMod = eval progDivMod eIniTest