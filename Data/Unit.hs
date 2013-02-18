{- | This module is used to express the fact that any tuple which is composed
     only from empty tuples holds the same amount of information as an empty
     tuple. -}
module Data.Unit where

{- | The unit class expresses the fact that all tuples composed from only empty
     tuples hold the same amount of information as the empty tuple and can thus
     all be constructed by a call to 'unit'. -}
class Unit t where
    -- | Constructs a unit type
    unit :: t

instance Unit () where
    unit = ()

instance (Unit a,Unit b) => Unit (a,b) where
    unit = (unit,unit)

instance (Unit a,Unit b,Unit c) => Unit (a,b,c) where
    unit = (unit,unit,unit)

instance (Unit a,Unit b,Unit c,Unit d) => Unit (a,b,c,d) where
    unit = (unit,unit,unit,unit)

instance (Unit a,Unit b,Unit c,Unit d,Unit e) => Unit (a,b,c,d,e) where
    unit = (unit,unit,unit,unit,unit)

instance (Unit a,Unit b,Unit c,Unit d,Unit e,Unit f) => Unit (a,b,c,d,e,f) where
    unit = (unit,unit,unit,unit,unit,unit)