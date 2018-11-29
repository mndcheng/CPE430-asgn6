include objects.fs

variable numVal
variable boolVal

object class \ "object" is the parent class
   selector pr ( -- )
   selector cls ( -- )
end-class exprC

exprC class
   cell% field val
   cell% 1 constant cl

   :noname ( -- )
      val @ . ;
   overrides pr

   :noname ( -- )
      cl ;
   overrides cls

   :noname ( num numC -- )
      val !
      val numVal ! ;
   overrides construct

end-class numC


exprC class
   cell% field b
   cell% 2 constant cl

   :noname ( -- )
      b @ . ;
   overrides pr

   :noname ( -- )
      cl ;
   overrides cls

   :noname ( bool boolC -- )
      b ! 
      b boolVal ! ;
   overrides construct

end-class boolC


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
my-num cls interp 

\ calling interp on boolC 
cr
my-bool cls interp

cr