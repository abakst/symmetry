module Render where

import           Prelude hiding (mapM, sequence, foldl, foldl')
import           Text.PrettyPrint.Leijen
import           Control.Monad.State     hiding (mapM, sequence)
import           Data.Maybe
import           Data.Traversable
import           Data.Foldable
import qualified Data.Map as M

import           AST  

-- | Some useful combinators
setSize :: Int
setSize = 2
x $$ y = align (x <$> y)
atomic :: [Doc] -> Doc
atomic ss = text "atomic" <+> braces (nest 0 $ (linebreak <> seqStmts ss))
block ds = braces (nest 2 $ seqStmts ds)

seqStmts :: [Doc] -> Doc
seqStmts ss = vcat . punctuate semi $ ss
         
-- | Rendering PIDs 
renderProcPrefix :: Pid -> Doc 
renderProcPrefix (PConc _)      = text "Proc_"
renderProcPrefix (PAbs _ (S s)) = text s
renderProcPrefix (PVar _)       = empty

renderProcName :: Pid -> Doc
renderProcName p@(PConc i)      = renderProcPrefix p <> int i
renderProcName p@(PAbs (V v) _) = renderProcPrefix p <> brackets (text v)
renderProcName p@(PVar (V v))   = renderProcPrefix p <> text v
                           
renderProcTypeName :: Pid -> Doc     
renderProcTypeName p@(PConc _) = renderProcName p <> text "_Process"
renderProcTypeName p@(PAbs _ _) = renderProcPrefix p <> text "_Process"

renderProcTypeArgs :: Pid -> Doc
renderProcTypeArgs p@(PConc _) = parens empty
renderProcTypeArgs p@(PAbs (V v) _) = parens (text "int" <+> text v)

renderPids  :: MType -> [Doc]
renderPids
  = map renderProcName . tyargs

-- | Messages
renderMType :: MType -> Doc
renderMType 
  = text . untycon . tycon
             
renderMsg :: MType -> Doc 
renderMsg m 
  = hcat $ punctuate comma (renderMType m : renderPids m)

renderMTypes :: [MType] -> Doc
renderMTypes ts
  = text "mtype" 
    <+> equals
    <+> encloseSep lbrace rbrace comma rts
    <+> semi
  where
    rts = map renderMType ts
          
-- | Addressing Process Channels
renderSwitchboard :: Int -> Int -> Doc
renderSwitchboard m n = text "chan" <+> text "switchboard" 
                                    <+> brackets (int (m * n))
                                    <> semi
             
switchboard :: Int -> Pid -> MType -> Doc 
switchboard np p m = 
  text "switchboard" <+> brackets (
                          (renderProcName p <> text "*" <> int np)
                          <+> text "+"
                          <+> parens (renderMType m <> text "-" <> int 1)
                         )

initSwitchboard :: Int -> Pid -> MType -> Doc
initSwitchboard n p@(PConc _) t
  = switchboard n p t <+> equals <+> renderChanName p t 
               
initSwitchboard n p@(PAbs (V v) (S s)) t
  = text "for" <+> parens (text v <+> text "in" <+> renderProcPrefix p) <> text "{" <$>
      (switchboard n p t <+> equals <+> renderChanName p t <> brackets (text v)) <$> text "}"
renderChanName :: Pid -> MType -> Doc                            
renderChanName p@(PConc _) t 
  = renderProcName p <> text "_" <> renderMType t
renderChanName p@(PAbs _ _) t 
  = renderProcPrefix p <> text "_" <> renderMType t
                                        
renderProcDecl n
  = text "int" <+> n
renderProcAssn n rhs 
  = renderProcDecl n <+> equals <+> rhs

-- | Emit Promela code for each statement    
renderStmt :: (Pid -> MType -> Doc) -> Pid -> Stmt a -> Doc
renderStmt f (p @ (PConc _)) s = renderStmtConc f p s
renderStmt f p s = renderStmtConc f p s
                   
renderStmtConc :: (Pid -> MType -> Doc) -> Pid -> Stmt a -> Doc
renderStmtConc f me (SSend p ms a)
  = text "if"
      $$ vcat (map go ms)
    <$> text "fi"
  where 
    go (m, s) = 
      text "::" <+> block (f p m <> text "!" <> renderMsg m
                          :map (renderStmt f me) s)
renderStmtConc f me (SRecv ms a)
  = text "if"
      $$ vcat (map go ms)
    <$> text "fi"
  where 
    go (m, s) = 
      text "::" <+> block (vars m ++ (f me m <> text "?" <> renderMsg m
                                     : map (renderStmt f me) s))
                                     
    vars m = 
      map (renderProcDecl . renderProcName) (tyargs m)
          
renderStmtConc f me (SSkip a)
  = text "skip"
    
renderStmtConc f me (SIter (V v) (S s) ss _)
  = text "int" <+> text ("__" ++ v) <> semi <$>
    text "int" <+> text v <> semi <$> 
    text "for" <+> parens (text ("__" ++ v) <+> text "in" <+> text s) <> text "{"
    $$ (text v <+> equals <+> renderProcName (PAbs (V ("__" ++ v)) (S s)) <> semi <$>
       (seqStmts $ map (renderStmt f me) ss))
    <$> text "}"
        
renderStmtConc f me (SLoop (V v) ss _)
  = text v <> text ":" <$>
     (block $ map (renderStmt f me) ss)
     
renderStmtConc f me (SVar (V v) _)
  = text "goto" <+> text v 
    
renderStmtConc f me (SChoose (V v) s ss _)
  = block [ text "int" <+> text v
          , text "select" <+> 
            parens (text v <+> text ":" <+> int 0 <+> text ".." <+> 
                                   int (setSize-1))
          , renderProcName (PVar (V v)) <+> equals <+> renderProcName (PAbs (V v) s)
          , (block $ map (renderStmt f me) ss)
          ]
    
          
renderStmtConc _ _ s
  = text "assert(0 == 1) /* TBD"

renderProcStmts :: (Pid -> MType -> Doc) -> Process a -> Doc
renderProcStmts f (p, ss) = seqStmts $ map (renderStmt f p) ss

renderProc :: (Pid -> MType -> Doc) -> Process a -> Doc
renderProc f p
  = let pr = renderProcStmts f p in
    text "proctype" 
           <+> renderProcTypeName (fst p)
           <+> renderProcTypeArgs (fst p)
           <$> block [pr]

renderProcs :: Config a -> Doc
renderProcs (Config ts _ ps)
  = foldl' (\d -> (d <$$>) . renderProc (switchboard (length ts)) ) empty ps
    
renderMain :: M.Map Pid Int -> Config a -> Doc
renderMain pidmap (Config ts _ ps) 
  = text "init" <+> block body
  where
    body              = declAbsVars ++
                        [ atomic pidInits
                        , atomic boardInits
                        , atomic procInits
                        ]
    declAbsVars       = [ text "int" <+> text v | PAbs (V v) _ <- map fst ps ]
    boardInits        = do p <- ps
                           t <- ts
                           return $ initSwitchboard (length ts) (fst p) t
    go p _ x  = x + sz p
    procInits = map (runProc . fst) ps
    pidInits  = fst $ foldl' (\(d,i) p -> 
                                (renderProcVar p i : d, i + sz p)) 
                             ([], 0) (map fst ps)
    sz (PConc _) = 1
    sz (PAbs _ _) = setSize
                        

runProc p@(PConc _) 
  = text "run" <+> 
    renderProcTypeName p <>
    parens empty

runProc p@(PAbs (V v) (S s) )
  = text "for" <+> parens (text v <+> text "in" <+> text s) <> text "{" <$> 
    text "run" <+>
    renderProcTypeName p <>
    parens (text v) <$>
    text "}"

renderProcVar :: Pid -> Int -> Doc                  
renderProcVar (PConc x) i
  = (renderProcName (PConc x)) <+> equals <+> (int i)
renderProcVar (PAbs v (S s)) i
  = seqStmts (map (uncurry go) (zip [0..setSize-1] [i..]))
  where
    go i j = text s <> brackets (int i) <+> equals <+> int j

declProcVar :: Pid -> Doc             
declProcVar p@(PConc _)
  = renderProcDecl (renderProcName p) <> semi
declProcVar p@(PAbs (V v) (S _a))
  = renderProcDecl (renderProcPrefix  p) <> brackets (int setSize) <> semi
             
declProcVars :: M.Map Pid Int -> Doc
declProcVars m
  = M.foldrWithKey go empty m
  where
    go pid _ d = declProcVar pid <$> d
                 

declChannels :: M.Map Pid Int -> [MType] -> Doc
declChannels pm ts 
  = vcat $ map (\t -> vcat $ map (go t) (M.keys pm)) ts
  where
    go t p@(PConc _) = text "chan" <+> renderChanName p t
                               <+> equals
                               <+> text "[1] of"
                               <+> encloseSep lbrace rbrace comma
                                     (text "mtype" : map (const (text "int")) (tyargs t))
                                     <> semi
    go t p@(PAbs _ _) = text "chan" <+> renderChanName p t <> brackets (int setSize)
                               <+> equals
                               <+> text "[1] of"
                               <+> encloseSep lbrace rbrace comma
                                     (text "mtype" : map (const (text "int")) (tyargs t))
                                     <> semi


buildPidMap :: [Pid] -> M.Map Pid Int
buildPidMap ps
  = fst $ foldl go (M.empty, 0) ps 
  where 
    go (m, i) p@(PConc _) = (M.insert p i m, succ i)
    go (m, i) p@(PAbs _ _) = (M.insert p i m, i + setSize)
                             
declSwitchboard :: M.Map Pid Int -> [MType] -> Doc
declSwitchboard pm ts
  = renderSwitchboard nprocs (length ts)
    where nprocs = 
            M.foldrWithKey (\p _ s -> s + count p) 0 pm
          count (PConc _)  = 1
          count (PAbs _ _) = setSize
  
render :: Show a => Config a -> Doc
render c@(Config ts ss ps)
  = mtype
    <$$> (text "#define __K__" <+> int setSize)
    <$$> declProcVars pidMap
    <$$> declChannels pidMap ts
    <$$> declSwitchboard pidMap ts
    <$$> procs
    <$$> renderMain pidMap c
  where
    pidMap   = buildPidMap (map fst ps)
    mtype    = renderMTypes ts
    procs    = renderProcs c
