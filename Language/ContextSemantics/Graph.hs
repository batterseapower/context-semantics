{-# LANGUAGE UndecidableInstances #-}

module Language.ContextSemantics.Graph where

import Language.ContextSemantics.Utilities

import qualified Data.IntMap as IM
import Data.List
import qualified Data.Traversable as T


--
-- Interactors: functors that we can build interaction graphs from
--

class Functor n => Interactor n where
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
    gr_root_port :: Port n
  }

foldNodewise :: Functor n => (n a -> a) -> Graph n -> a
foldNodewise f gr = lookup_node (gr_root_port gr)
  where lookup_node port = assertJust "foldNodewise" (IM.lookup (port_node port) node_vals)
        node_vals = IM.map (f . fmap lookup_node) (gr_nodes gr)

foldPortwise :: Interactor n => (n a -> n a) -> Graph n -> a
foldPortwise f gr = lookup_port (gr_root_port gr)
  where lookup_port port = port_selector port `select` assertJust "foldPortwise" (IM.lookup (port_node port) node_port_vals)
        node_port_vals = IM.map (f . fmap lookup_port) (gr_nodes gr)


--
-- Graph builder monad, for convenience
--

newtype Wire = Wire Int
             deriving (Show)

data GraphBuilderEnv n = GraphBuilderEnv {
    gbe_next_unique :: Int,
    gbe_wire_eq_class :: IM.IntMap Int,
    gbe_eq_class_ports :: IM.IntMap [Port n],
    gbe_nodes :: IM.IntMap (n Wire)
  }

emptyGraphBuilderEnv :: GraphBuilderEnv n
emptyGraphBuilderEnv = GraphBuilderEnv {
    gbe_next_unique = 0,
    gbe_wire_eq_class = IM.empty,
    gbe_eq_class_ports = IM.empty,
    gbe_nodes = IM.empty
  }

newtype GraphBuilderM n a = GraphBuilderM {
    unGraphBuilderM :: GraphBuilderEnv n -> (GraphBuilderEnv n, a)
  }

instance Monad (GraphBuilderM n) where
    return x = GraphBuilderM $ \env -> (env, x)
    mx >>= f = GraphBuilderM $ \env -> case unGraphBuilderM mx env of (env', y) -> unGraphBuilderM (f y) env'

newUnique :: GraphBuilderM n Int
newUnique = GraphBuilderM $ \env -> let i = gbe_next_unique env in (env { gbe_next_unique = i + 1 }, i)

insertNode :: Int -> n Wire -> GraphBuilderM n ()
insertNode i node = GraphBuilderM $ \env -> (env { gbe_nodes = IM.insert i node (gbe_nodes env) }, ())

recordWireConnection :: Port n -> Wire -> GraphBuilderM n ()
recordWireConnection p (Wire wire) = GraphBuilderM $ \env ->
    let equiv   = iMlookupCertainly wire (gbe_wire_eq_class env)
        classes = iMlookupCertainly equiv (gbe_eq_class_ports env)
        
        env' = env { gbe_eq_class_ports = IM.insert equiv (p : classes) (gbe_eq_class_ports env) }
    in (env', ())

newWire :: GraphBuilderM a Wire
newWire = do
    i <- newUnique
    GraphBuilderM $ \env -> (env { gbe_wire_eq_class = IM.insert i i (gbe_wire_eq_class env)
                                 , gbe_eq_class_ports = IM.insert i [] (gbe_eq_class_ports env) }, Wire i)

newNode :: (Interactor n, T.Traversable n) => n Wire -> GraphBuilderM n ()
newNode init_wires = do
    nid <- newUnique
    insertNode nid init_wires
    fmapM_ (\(selector, init_wire) -> recordWireConnection (Port nid selector) init_wire) (selectors init_wires)

join :: Wire -> Wire -> GraphBuilderM n ()
join (Wire wire1) (Wire wire2) = GraphBuilderM $ \env -> 
    let (equiv1, equiv2)     = (iMlookupCertainly wire1 (gbe_wire_eq_class env),   iMlookupCertainly wire2 (gbe_wire_eq_class env))
        (classes1, classes2) = (iMlookupCertainly equiv1 (gbe_eq_class_ports env), iMlookupCertainly equiv2 (gbe_eq_class_ports env))
      
        classes' = classes1 ++ classes2
        env' = env { gbe_wire_eq_class = IM.insert wire2 equiv1 (gbe_wire_eq_class env)
                   , gbe_eq_class_ports = IM.insert equiv1 classes' (IM.delete equiv2 (gbe_eq_class_ports env)) }
    in (env', ())

runGraphBuilderM :: (Interactor n, Functor n, Show (Selector n), Eq (Selector n)) => GraphBuilderM n Wire -> Graph n
runGraphBuilderM mx = Graph {
      gr_nodes = nodes,
      gr_root_port = fromSingleton (lookupAllWirePorts root_wire)
    }
  where (final_env, root_wire) = unGraphBuilderM mx emptyGraphBuilderEnv
        
        nodes = IM.mapWithKey (\nid -> fmap (\(sel, wire) -> lookupWirePort (Port nid sel) wire) . selectors) (gbe_nodes final_env)
        lookupAllWirePorts (Wire wire) = iMlookupCertainly (iMlookupCertainly wire (gbe_wire_eq_class final_env)) (gbe_eq_class_ports final_env)
        lookupWirePort this_port wire = case filter ((/=) this_port) all_ports of
                                      [port] -> port
                                      []     -> error $ "No suitable ports were set up for " ++ show this_port ++ ", wire " ++ show wire ++ " - this should be impossible (we had ports for nodes " ++ show all_ports ++ ")" -- show (map port_node all_ports) ++ ")"
                                      _      -> error $ "Too many ports were set up for a wire - we got ports for nodes " ++ show (map port_node all_ports) ++ " while looking for the other end of node " ++ show (port_node this_port)
          where all_ports = lookupAllWirePorts wire