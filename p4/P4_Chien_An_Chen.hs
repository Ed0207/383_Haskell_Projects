import Prelude
import System.IO
import System.Environment
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Control.Monad.State.Lazy

type VarId = String

data Type = TInt
            | TBool
            | TError
            | TVar Int
            | TArr Type Type
            deriving (Eq, Ord, Read, Show)

data Constraint = CEq Type Type
                    | CError
                    deriving (Eq, Ord, Read, Show)

type ConstraintSet = Set.Set Constraint
type ConstraintList = [Constraint]

data Expr = CInt Int
            | CBool Bool
            | Var VarId
            | Plus Expr Expr
            | Minus Expr Expr
            | Equal Expr Expr
            | ITE Expr Expr Expr
            | Abs VarId Expr
            | App Expr Expr
            | LetIn VarId Expr Expr
            deriving (Eq, Ord, Read, Show)

type Env = Map.Map VarId Type
type InferState a = State Int a 
type Substitution = Map.Map Type Type





-- assignment starts here
-- note to self, n is current state with integer, put defines the next state with integer
getFreshTVar :: InferState Type
getFreshTVar = do   n <- get
                    put (n+1)
                    return (TVar n)


-- rename variable name to have clearer understanding of the function
infer :: Env -> Expr -> InferState (Type, ConstraintSet)
infer env (CInt _)          = return (TInt, Set.empty)
infer env (Abs newVar expr) = do    newTypeVar <- getFreshTVar
                                    (t, c) <- infer (Map.insert newVar newTypeVar env) expr
                                    return (TArr newTypeVar t, c)


-- follow the given constraint on the P4 
infer env (CBool _)         = return (TBool, Set.empty)
infer env (Plus a b)        = do    (t1, c1) <- infer env a
                                    (t2, c2) <- infer env b
                                    return (TInt, Set.insert (CEq t2 TInt) (Set.insert (CEq t1 TInt) (Set.union c1 c2)))
infer env (Minus a b)       = do    (t1, c1) <- infer env a
                                    (t2, c2) <- infer env b
                                    return (TInt, Set.insert (CEq t2 TInt) (Set.insert (CEq t1 TInt) (Set.union c1 c2)))
infer env (Equal a b)       = do    (t1, c1) <- infer env a
                                    (t2, c2) <- infer env b
                                    return (TBool, Set.insert (CEq t1 t2)  (Set.union c1 c2))
-- LetIn "x" (CInt 1) (Var "x")
infer env (LetIn newVar a b) = do   newTypeVar <- getFreshTVar
                                    (t1, c1) <- infer (Map.insert newVar newTypeVar env) a
                                    (t2, c2) <- infer (Map.insert newVar newTypeVar env) b
                                    return (t2, (Set.insert (CEq newTypeVar t1)  (Set.union c1 c2)))
infer env (ITE cond a b)    = do    (t1, c1) <- infer env cond
                                    (t2, c2) <- infer env a
                                    (t3, c3) <- infer env b 
                                    return (t2, (Set.insert (CEq t2 t3) (Set.insert (CEq t1 TBool) (Set.union c3 (Set.union c1 c2)))))
-- App (Abs "x" (Var "x")) (CInt 1)
infer env (App a b)         = do    (t1, c1) <- infer env a
                                    (t2, c2) <- infer env b
                                    x1 <- getFreshTVar
                                    x2 <- getFreshTVar
                                    return (x2, ((Set.insert (CEq t1 (TArr x1 x2)) (Set.insert (CEq t2 x1) (Set.union c1 c2)))))
infer env (Var varID)       = do    case Map.lookup varID env of
                                        Nothing -> return (TError, Set.singleton CError)
                                        Just x  -> return (x, Set.empty)


inferExpr :: Expr -> (Type, ConstraintSet)
inferExpr expr = evalState (infer Map.empty expr) 1


toCstrList :: ConstraintSet -> ConstraintList
toCstrList conSet = Set.toList conSet


-- slide 20 p24
applySub :: Substitution -> Type -> Type
applySub subs var = case var of
                        TError      -> TError
                        TInt        -> TInt
                        TBool       -> TBool
                        (TArr a b)  -> (TArr (applySub subs a) (applySub subs b))
                        (TVar a)    -> case Map.lookup (TVar a) subs of
                                        Just t  -> t
                                        Nothing -> (TVar a)


applySubToCstrList :: Substitution -> ConstraintList -> ConstraintList
applySubToCstrList subs (c:cs)  = case c of 
                                    (CEq a b)           -> (CEq (applySub subs a) (applySub subs b)) : (applySubToCstrList subs cs)
                                    CError              -> CError : (applySubToCstrList subs cs)
applySubToCstrList _ cList      = cList


composeSub :: Substitution -> Substitution -> Substitution
composeSub sub1 sub2 = Map.union sub1 sub2


tvars ::  Type -> Set.Set Type
tvars TInt          = Set.empty
tvars TBool         = Set.empty
tvars TError        = Set.insert TError Set.empty
tvars (TVar a)      = Set.insert (TVar a) Set.empty
tvars (TArr a b)    = Set.union (tvars a) (tvars b)


-- follow the slide 20 p28 algorithm
unify :: ConstraintList -> Maybe Substitution 
unify conList = case conList of
    []              -> Just Map.empty
    (CError:cs)     -> Nothing
    ((CEq s t):cs)  -> unifyAux (CEq s t) cs


-- for reference, Substitution = Map.Map Type Type
-- follow the slide 20 p28 algorithm
unifyAux :: Constraint -> ConstraintList -> Maybe Substitution 
unifyAux (CEq s t) cs = if s == t then (unify cs) else case s of 
                                                        (TVar a)        -> if (Set.member (TVar a) (tvars t)) then Nothing else case unify (applySubToCstrList (Map.insert (TVar a) t Map.empty) cs) of
                                                                                                                                    Just subs -> Just (Map.insert (TVar a) t subs)
                                                                                                                                    Nothing   -> Nothing
                                                        (TArr s1 s2)    -> case t of
                                                                            (TArr t1 t2) -> unify (cs ++ [(CEq s1 t1)] ++ [(CEq s2 t2)])
                                                                            _            -> Nothing
                                                        _               -> case t of
                                                                            (TVar a)     -> if (Set.member (TVar a) (tvars s)) then Nothing else case unify (applySubToCstrList (Map.insert (TVar a) s Map.empty) cs) of
                                                                                                                                                    Just subs -> Just (Map.insert (TVar a) s subs)
                                                                                                                                                    Nothing   -> Nothing
                                                                            _            -> Nothing


typing :: Expr -> Maybe Type
typing expr = case unify (toCstrList constraintSet) of 
                Just subs  -> Just (applySub subs resultType)
                Nothing    -> Nothing
    where   (resultType, constraintSet) = inferExpr expr


typeInfer :: Expr -> String
typeInfer expr = case result of
                    Just x  -> show (relabel x)
                    Nothing -> "Type Error" 
    where result = typing expr 




-- main logic, no need to modify 

testProgram :: String -> String
testProgram [] = []
testProgram s = typeInfer (readExpr s)

readExpr :: String -> Expr
readExpr s = read s::Expr

processExpr :: [String] -> String
processExpr [] = []
processExpr (x:xs) = typeInfer (readExpr x) ++ "\n" ++ processExpr xs

main :: IO()
main =  do   
    fileName <- getArgs
    handle <- openFile (head fileName) ReadMode
    contents <- hGetContents handle
    let ls = lines contents
    putStr (processExpr ls)
    hClose handle   






--Apendix
type RelabelState a = State (Map.Map Int Int) a

relabel :: Type -> Type
relabel t = evalState (go t) Map.empty
    where
        go :: Type -> RelabelState Type
        go TInt = return TInt
        go TBool = return TBool
        go TError = return TError
        go (TVar x) = do    m <- get
                            case Map.lookup x m of
                                Just v -> return (TVar v)
                                Nothing -> do   let n = 1 + Map.size m
                                                put (Map.insert x n m)
                                                return (TVar n)
        go (TArr t1 t2) = do    t1' <- go t1
                                t2' <- go t2
                                return (TArr t1' t2')
