include objects.fs

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
      cl . ;
   overrides cls

   :noname ( num numC -- )
      val ! ;
   overrides construct

end-class numC


exprC class
   cell% field b
   cell% 2 constant cl

   :noname ( -- )
      b @ . ;
   overrides pr

   :noname ( -- )
      cl . ;
   overrides cls

   :noname ( bool boolC -- )
      b ! ;
   overrides construct

end-class boolC


