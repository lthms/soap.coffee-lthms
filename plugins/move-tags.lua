tags = HTML.select_one(page, "#tags-list")
title = HTML.select_one(page, "h1")

if tags and title then
  HTML.delete(tags)
  HTML.insert_after(title, tags)
end
