with Ada.Text_IO; use Ada.Text_IO;

procedure Days_Of_Week is
    type Day_Of_Week is (Monday, Tuesday, Wednesday, Thursday, Friday, Saturday, Sunday);
begin
    for Day in Day_Of_Week loop
        Put_Line(Day'Image);
    end loop;
end Days_Of_Week;
