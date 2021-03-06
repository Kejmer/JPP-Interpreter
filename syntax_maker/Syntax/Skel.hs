-- Haskell module generated by the BNF converter

{-# OPTIONS_GHC -fno-warn-unused-matches #-}

module Syntax.Skel where

import Prelude (($), Either(..), String, (++), Show, show)
import qualified Syntax.Abs

type Err = Either String
type Result = Err String

failure :: Show a => a -> Result
failure x = Left $ "Undefined case: " ++ show x

transIdent :: Syntax.Abs.Ident -> Result
transIdent x = case x of
  Syntax.Abs.Ident string -> failure x

transProgram :: Syntax.Abs.Program -> Result
transProgram x = case x of
  Syntax.Abs.MyProgram stmts -> failure x

transBlock :: Syntax.Abs.Block -> Result
transBlock x = case x of
  Syntax.Abs.Blok stmts -> failure x

transHBlock :: Syntax.Abs.HBlock -> Result
transHBlock x = case x of
  Syntax.Abs.AsProc pblock -> failure x
  Syntax.Abs.AsStmt stmt -> failure x

transStmt :: Syntax.Abs.Stmt -> Result
transStmt x = case x of
  Syntax.Abs.BStmt block -> failure x
  Syntax.Abs.DeclMut basictype ident expr -> failure x
  Syntax.Abs.DeclConst basictype ident expr -> failure x
  Syntax.Abs.Ass ident expr -> failure x
  Syntax.Abs.ArrAss ident expr1 expr2 -> failure x
  Syntax.Abs.Ret expr -> failure x
  Syntax.Abs.If expr hblock -> failure x
  Syntax.Abs.IfElse expr hblock1 hblock2 -> failure x
  Syntax.Abs.While expr hblock -> failure x
  Syntax.Abs.Print expr -> failure x
  Syntax.Abs.For expr proc_ -> failure x
  Syntax.Abs.SExp expr -> failure x
  Syntax.Abs.FDef basictype ident args pblock -> failure x
  Syntax.Abs.FDefAlt basictype ident args lambda -> failure x

transType :: Syntax.Abs.Type -> Result
transType x = case x of
  Syntax.Abs.Ref basictype -> failure x
  Syntax.Abs.MutRef basictype -> failure x
  Syntax.Abs.Mut basictype -> failure x
  Syntax.Abs.Const basictype -> failure x

transBasicType :: Syntax.Abs.BasicType -> Result
transBasicType x = case x of
  Syntax.Abs.Arr basictype -> failure x
  Syntax.Abs.Int -> failure x
  Syntax.Abs.Str -> failure x
  Syntax.Abs.Bool -> failure x
  Syntax.Abs.Void -> failure x
  Syntax.Abs.Fun basictype types -> failure x
  Syntax.Abs.TProc basictype args types -> failure x

transProc :: Syntax.Abs.Proc -> Result
transProc x = case x of
  Syntax.Abs.PDec args1 args2 block -> failure x

transLambda :: Syntax.Abs.Lambda -> Result
transLambda x = case x of
  Syntax.Abs.LDec basictype args block -> failure x

transPBlock :: Syntax.Abs.PBlock -> Result
transPBlock x = case x of
  Syntax.Abs.FProc proc_ -> failure x
  Syntax.Abs.FBlok block -> failure x
  Syntax.Abs.FVar ident -> failure x

transArg :: Syntax.Abs.Arg -> Result
transArg x = case x of
  Syntax.Abs.FArg type_ ident -> failure x

transExpr :: Syntax.Abs.Expr -> Result
transExpr x = case x of
  Syntax.Abs.ERange expr1 expr2 -> failure x
  Syntax.Abs.EVar ident -> failure x
  Syntax.Abs.EInt integer -> failure x
  Syntax.Abs.ETrue -> failure x
  Syntax.Abs.EFalse -> failure x
  Syntax.Abs.EString string -> failure x
  Syntax.Abs.EParen expr -> failure x
  Syntax.Abs.EProc proc_ -> failure x
  Syntax.Abs.ELamb lambda -> failure x
  Syntax.Abs.ECall expr exprs -> failure x
  Syntax.Abs.EStringify expr -> failure x
  Syntax.Abs.EArr exprs -> failure x
  Syntax.Abs.EArrRead ident expr -> failure x
  Syntax.Abs.Neg expr -> failure x
  Syntax.Abs.Not expr -> failure x
  Syntax.Abs.EMul expr1 mulop expr2 -> failure x
  Syntax.Abs.EAdd expr1 addop expr2 -> failure x
  Syntax.Abs.EComp expr1 compop expr2 -> failure x
  Syntax.Abs.EAnd expr1 expr2 -> failure x
  Syntax.Abs.EOr expr1 expr2 -> failure x

transAddOp :: Syntax.Abs.AddOp -> Result
transAddOp x = case x of
  Syntax.Abs.Plus -> failure x
  Syntax.Abs.Minus -> failure x

transMulOp :: Syntax.Abs.MulOp -> Result
transMulOp x = case x of
  Syntax.Abs.Times -> failure x
  Syntax.Abs.Div -> failure x
  Syntax.Abs.Mod -> failure x

transCompOp :: Syntax.Abs.CompOp -> Result
transCompOp x = case x of
  Syntax.Abs.Low -> failure x
  Syntax.Abs.Grt -> failure x
  Syntax.Abs.LowEq -> failure x
  Syntax.Abs.GrtEq -> failure x
  Syntax.Abs.Eq -> failure x
  Syntax.Abs.NEq -> failure x
