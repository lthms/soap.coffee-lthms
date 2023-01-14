notes = HTML.select_all_of(page, {".marginnote", ".sidenote"})

local index = 1
while notes[index] do
  local note = notes[index]

  HTML.add_class(note, "note")

  index = index + 1
end

notes = HTML.select(page, ".note")
index = 1
while notes[index] do
  local note = notes[index]

  if index % 2 == 0 then
    HTML.add_class(note, "note-right")
  else
    HTML.add_class(note, "note-left")
  end

  index = index + 1
end