include objects.fs

variable numVal
variable boolVal

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
      val !
      val numVal ! ;
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
      val ! 
      val boolVal ! ;
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


: interp ( exprC -- value )
   dup 1 = if                        numVal ?   else
   dup 2 = boolVal 0 = and if        ." false"  else
   dup 2 = boolVal 0 = invert and if ." true"   else
                                     ." error"
   then then then drop ; 


24 numC heap-new constant my-num \ new numC
-1 boolC heap-new constant my-bool \ new boolC 

\ calling interp on numC 
cr
my-num typ interp 

\ calling interp on boolC 
cr
my-bool typ interp

cr