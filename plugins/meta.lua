description = HTML.select_one(page, "#meta-tags .description")

if description then
  description_contents = HTML.strip_tags(description)
  head = HTML.select_one(page, "head")
  HTML.append_child(head, HTML.parse('<meta type="description" content="' .. description_contents .. '">'))
else
  Log.warning("Missing description in " .. page_file)
end

HTML.delete(description)

timestamps = HTML.select_one(page, "#timestamps")

if timestamps then
  HTML.delete(timestamps)
  target = HTML.select_one(page, "#whoami")
  HTML.insert_after(target, timestamps)
end
