include objects.fs

object class \ "object" is the parent class
   selector objValue ( -- )
   selector objType ( -- )
end-class exprC

exprC class
   cell% field val
   cell% 1 constant typ

   :noname ( -- )
      val @ ;
   overrides objValue

   :noname ( -- )
      typ ;
   overrides objType

   :noname ( num numC -- )
      val ! ;
   overrides construct

end-class numC


exprC class
   cell% field val
   cell% 2 constant typ

   :noname ( -- )
      val @ ;
   overrides objValue

   :noname ( -- )
      typ ;
   overrides objType

   :noname ( bool boolC -- )
      val ! ;
   overrides construct

end-class boolC


exprC class
   cell% field val
   cell% 3 constant typ

   :noname ( -- )
      val @ ;
   overrides objValue

   :noname ( -- )
      typ ;
   overrides objType

   :noname ( str stringC -- )
      val ! ;
   overrides construct

end-class stringC
