module Data.Unit where

class Unit t where
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