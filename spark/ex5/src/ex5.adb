-- prove w/ alr gnatprove -j0 -cargs -gnato13
with Ada.Command_Line; use Ada.Command_Line;
with Ada.Text_IO; use Ada.Text_IO;

procedure Ex5 with SPARK_Mode is

   -- Let's add specifications to ensure no overflow
   function timestwo (X : Integer) return Integer with
      Pre => X >= 0 and then X <= Integer'Last / 2,
      Post => timestwo'Result = X * 2 and then
              timestwo'Result <= Integer'Last;

   function timestwo (X : Integer) return Integer is
   begin
      return X * 2;
   end timestwo;

   x1 : Integer;
   x2 : Integer;

begin
   if Argument_Count /= 1 then
      Put_Line ("Usage: ex5 <integer>");
      return;
   else
      x1 := Integer'Value (Argument (1));

      if x1 > Integer'Last / 2 then
         Put_Line ("Error: Integer too large");
         return;
      elsif x1 < 0 then
         Put_Line ("Error: Integer must be positive");
         return;
      else
         pragma Assert (x1 >= 0 and then x1 <= Integer'Last / 2);
         x2 := timestwo (x1);
      end if;

   end if;

   Put_Line (Integer'Image (x2));
end Ex5;