-- show proof with `alr gnatprove -j0`
with Ada.Command_Line; use Ada.Command_Line;
with Ada.Text_IO; use Ada.Text_IO;

procedure Ex4 with SPARK_Mode is

   function timestwo (X : Integer) return Integer is
   begin
      return X * 2;
   end timestwo;

   x : Integer;
begin
   x := timestwo (Integer'Value (Argument (1)));

   Put_Line (Integer'Image (x));
end Ex4;
