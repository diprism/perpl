module Polymorphism where
import qualified Data.Map as Map
import Data.List
import Exprs

{- Functions for finding all instances of polymorphic types -}

-- Records an instantiation of a polymorphic type
piAppend :: Var -> [Type] -> Map.Map Var [[Type]] -> Map.Map Var [[Type]]
piAppend y tp pis = Map.insertWith (++) y [tp] pis

-- Retrieves all instantiations of polymorphic types (e.g. Maybe [...]) in a term
getPolyInstsTerm :: Map.Map Var [[Type]] -> Term -> Map.Map Var [[Type]]
getPolyInstsTerm pis (TmVarL x tp) = getPolyInstsType pis tp
getPolyInstsTerm pis (TmVarG gv x as tp) = foldl (\ pis (a, atp) -> getPolyInstsTerm pis a) (getPolyInstsType pis tp) as
getPolyInstsTerm pis (TmLam x tp tm tp') = getPolyInstsTerm (getPolyInstsType pis tp) tm -- no need to do tp' bc tm already adds all insts
getPolyInstsTerm pis (TmApp tm1 tm2 tp2 tp) = getPolyInstsTerm (getPolyInstsTerm pis tm2) tm1
getPolyInstsTerm pis (TmLet x xtm xtp tm tp) = getPolyInstsTerm (getPolyInstsTerm pis xtm) tm
getPolyInstsTerm pis (TmCase tm y cs tp) =
  foldl (\ pis (Case x as ctm) -> getPolyInstsTerm pis ctm)
    (getPolyInstsType (getPolyInstsTerm pis tm) y) cs
getPolyInstsTerm pis (TmSamp d tp) = getPolyInstsType pis tp
getPolyInstsTerm pis (TmAmb tms tp) = foldl (\ pis tm -> getPolyInstsTerm pis tm) (getPolyInstsType pis tp) tms

-- Retrives all instantiations of polymorphic types (e.g. Maybe [...]) in a type
getPolyInstsType :: Map.Map Var [[Type]] -> Type -> Map.Map Var [[Type]]
getPolyInstsType pis (TpVar y) = pis
getPolyInstsType pis (TpArr tp1 tp2) = getPolyInstsType (getPolyInstsType pis tp1) tp2
getPolyInstsType pis (TpMaybe tp) = piAppend tpMaybeName [tp] (getPolyInstsType pis tp)

-- Retrives all instantiations of polymorphic types (e.g. Maybe [...]) in a Prog
getPolyInstsProg :: Map.Map Var [[Type]] -> Prog -> Map.Map Var [[Type]]
getPolyInstsProg pis (ProgFun x ps tm tp) = foldl getPolyInstsType (getPolyInstsTerm pis tm) (map snd ps)
getPolyInstsProg pis (ProgExtern x xp ps tp) = foldl getPolyInstsType (getPolyInstsType pis tp) ps
getPolyInstsProg pis (ProgData y cs) = foldl (\ pis (Ctor x as) -> foldl getPolyInstsType pis as) pis cs

getPolyInstsProgs :: Map.Map Var [[Type]] -> Progs -> Map.Map Var [[Type]]
getPolyInstsProgs pis (Progs ps tm) = Map.unionsWith (++) (getPolyInstsTerm pis tm : map (getPolyInstsProg pis) ps)

-- Retrives all instantiations of a particular polymorphic type var (e.g. Maybe [...])
getPolyInsts :: Progs -> Var -> [[Type]]
getPolyInsts ps y =
  let is = getPolyInstsProgs Map.empty ps in
    maybe [] nub (Map.lookup y is)
