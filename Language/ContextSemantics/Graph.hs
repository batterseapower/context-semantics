{-# LANGUAGE UndecidableInstances #-}

module Language.ContextSemantics.Graph where

import Language.ContextSemantics.Utilities

import Control.Arrow (second)
import Control.Monad

import qualified Data.IntMap as IM
import qualified Data.Foldable as F
import Data.List
import qualified Data.Traversable as T


--
-- Interactors: functors that we can build interaction graphs from
--

class (T.Traversable n, Eq (Selector n)) => Interactor n where
  type Selector n :: *
  
  selectors :: n a -> n (Selector n, a)
  select :: Selector n -> n a -> a


--
-- Interaction graphs
--

type NodeId = Int

data Port n = Port {
    port_node :: NodeId,
    port_selector :: Selector n
  }

-- Requires UndecidableInstances
instance Show (Selector n) => Show (Port n) where
    show port = show (port_node port) ++ "." ++ show (port_selector port)

-- Requires UndecidableInstances
instance Eq (Selector n) => Eq (Port n) where
    p1 == p2 = port_node p1 == port_node p2 &&
               port_selector p1 == port_selector p2

data Graph n = Graph {
    gr_nodes :: IM.IntMap (n (Port n)),
    gr_named_ports :: [(String, Port n)]
  }

foldNodewise :: Functor n => (n a -> a) -> Graph n -> [(String, a)]
foldNodewise f gr = map (second lookup_node) (gr_named_ports gr)
  where lookup_node port = assertJust "foldNodewise" (IM.lookup (port_node port) node_vals)
        node_vals = IM.map (f . fmap lookup_node) (gr_nodes gr)

foldPortwise :: Interactor n => (n a -> n a) -> Graph n -> [(String, a)]
foldPortwise f gr = map (second lookup_port) (gr_named_ports gr)
  where lookup_port port = port_selector port `select` assertJust "foldPortwise" (IM.lookup (port_node port) node_port_vals)
        node_port_vals = IM.map (f . fmap lookup_port) (gr_nodes gr)


--
-- Converting to .dot files
--

toDot :: Interactor n
      => (n () -> [(String, String)])                     -- ^ Assignment of attributes to node
      -> (Selector n -> Selector n -> [(String, String)]) -- ^ Assignment of attributes to edges
      -> Graph n
      -> String
toDot node_attrs edge_attrs gr = "graph {\r\n" ++ intercalate ";\r\n" statements ++ "\r\n}\r\n"
  where nodes = IM.assocs (gr_nodes gr)
        edges = [(Port from_nid from_selector, to_port)
                | (from_nid, from_n) <- nodes
                , (from_selector, to_port) <- F.toList (selectors from_n)]
        unique_edges = nubBy (\(p1, p2) (q1, q2) -> (p1 == q1 && p2 == q2) || (p1 == q2 && p2 == q1)) edges
        
        statements = named_node_statements ++ named_edge_statements ++ node_statements ++ edge_statements
        named_node_statements = ["named" ++ name ++ " [shape=point,label=" ++ name ++ "]"
                                | (name, _) <- gr_named_ports gr]
        named_edge_statements = ["named" ++ name ++ " -- node" ++ show (port_node port) ++ " [arrowhead=normal]"
                                | (name, port) <- gr_named_ports gr]
        node_statements = ["node" ++ show nid ++ format_list (("label", show nid) : node_attrs (fmap (const ()) n))
                          | (nid, n) <- nodes]
        edge_statements = ["node" ++ show (port_node from_port) ++ " -- node" ++ show (port_node to_port) ++ " " ++ format_list (edge_attrs (port_selector from_port) (port_selector to_port))
                          | (from_port, to_port) <- unique_edges]
        format_list avps = "[" ++ intercalate "," [attr ++ "=" ++ val | (attr, val) <- avps] ++ "]"


--
-- Graph builder monad, for convenience of construction
--

newtype LooseEnd = LooseEnd { unLooseEnd :: Int }
                 deriving (Show)

data Knot n = KnotToLooseEnd LooseEnd
            | KnotToPort (Port n)

data GraphBuilderEnv n = GraphBuilderEnv {
    gbe_next_unique :: Int,
    gbe_loose_end_joins :: IM.IntMap LooseEnd,
    gbe_loose_ends :: IM.IntMap (Maybe (Knot n)),
    gbe_nodes :: IM.IntMap (n LooseEnd)
  }

emptyGraphBuilderEnv :: GraphBuilderEnv n
emptyGraphBuilderEnv = GraphBuilderEnv {
    gbe_next_unique = 0,
    gbe_loose_end_joins = IM.empty,
    gbe_loose_ends = IM.empty,
    gbe_nodes = IM.empty
  }

newtype GraphBuilderM n a = GraphBuilderM {
    unGraphBuilderM :: GraphBuilderEnv n -> (GraphBuilderEnv n, a)
  }

instance Functor (GraphBuilderM n) where
    fmap f mx = mx >>= \x -> return (f x)

instance Monad (GraphBuilderM n) where
    return x = GraphBuilderM $ \env -> (env, x)
    mx >>= f = GraphBuilderM $ \env -> case unGraphBuilderM mx env of (env', y) -> unGraphBuilderM (f y) env'

newUnique :: GraphBuilderM n Int
newUnique = GraphBuilderM $ \env -> let i = gbe_next_unique env in (env { gbe_next_unique = i + 1 }, i)

insertNode :: Int -> n LooseEnd -> GraphBuilderM n ()
insertNode i node = GraphBuilderM $ \env -> (env { gbe_nodes = IM.insert i node (gbe_nodes env) }, ())

knotOnce :: a -> Maybe a -> Maybe a
knotOnce what Nothing  = Just what
knotOnce _    (Just _) = error "Can't knot a loose end twice!"

knotLooseEndToPort :: LooseEnd -> Port n -> GraphBuilderM n ()
knotLooseEndToPort le p = GraphBuilderM $ \env -> (env { gbe_loose_ends = IM.adjust (knotOnce (KnotToPort p)) (unLooseEnd le) (gbe_loose_ends env) }, ())

knotLooseEnds :: LooseEnd -> LooseEnd -> GraphBuilderM n ()
knotLooseEnds le1 le2 = GraphBuilderM $ \env -> (env { gbe_loose_ends = IM.adjust (knotOnce (KnotToLooseEnd le1)) (unLooseEnd le2) (IM.adjust (knotOnce (KnotToLooseEnd le2)) (unLooseEnd le1) (gbe_loose_ends env)) }, ())

newWire :: GraphBuilderM a (LooseEnd, LooseEnd)
newWire = do
    le1 <- liftM LooseEnd newUnique
    le2 <- liftM LooseEnd newUnique
    GraphBuilderM $ \env -> (env { gbe_loose_end_joins = IM.insert (unLooseEnd le2) le1 (IM.insert (unLooseEnd le1) le2 (gbe_loose_end_joins env))
                                 , gbe_loose_ends = IM.insert (unLooseEnd le1) Nothing (IM.insert (unLooseEnd le2) Nothing (gbe_loose_ends env)) }, (le1, le2))

newNode :: Interactor n => n LooseEnd -> GraphBuilderM n ()
newNode n_loose_ends = do
    nid <- newUnique
    insertNode nid n_loose_ends
    fmapM_ (\(selector, loose_end) -> knotLooseEndToPort loose_end (Port nid selector)) (selectors n_loose_ends)

join :: LooseEnd -> LooseEnd -> GraphBuilderM n ()
join = knotLooseEnds

runGraphBuilderM :: Interactor n => GraphBuilderM n [(String, LooseEnd)] -> Graph n
runGraphBuilderM mx = Graph {
      gr_nodes = nodes,
      gr_named_ports = map (second lookupLooseEndPort) named_les
    }
  where (final_env, named_les) = unGraphBuilderM mx emptyGraphBuilderEnv
        
        nodes = IM.map (fmap lookupLooseEndPort) (gbe_nodes final_env)
        lookupLooseEndPort le = case iMlookupCertainly (unLooseEnd $ iMlookupCertainly (unLooseEnd le) (gbe_loose_end_joins final_env)) (gbe_loose_ends final_env) of
                                    Nothing                   -> error $ "An unknotted loose end remained!"
                                    Just (KnotToLooseEnd le') -> lookupLooseEndPort le'
                                    Just (KnotToPort p)       -> p
