notes = HTML.select_all_of(page, {".marginblock", ".sidenote"})

local index = 1
while notes[index] do
  local note = notes[index]

  HTML.add_class(note, "note")

  index = index + 1
end

ofs = 0
notes = HTML.select(page, ".note")
index = 1
while notes[index] do
  local note = notes[index]

  if (index + ofs) % 2 == 0 then
    HTML.add_class(note, "note-right")
  else
    HTML.add_class(note, "note-left")
  end

  index = index + 1

  -- the first margin note component (the avatar) takes a lot more space than
  -- the second one (update dates and tags), so it's interesting that the first
  -- note after these ones is also on the right.
  if index == 3 then
    ofs = 1
  end
end
