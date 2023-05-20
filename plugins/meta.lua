base_url = config['site_base_url'] ..
  soupault_config['widgets']['urls-rewriting']['prefix_url']

head = HTML.select_one(page, "head")

title = HTML.select_one(page, 'h1')
if title then
  HTML.append_child(
    head,
    HTML.parse(
      '<meta property="og:title" content="'  .. HTML.strip_tags(title) .. '" />'
    )
  )
  HTML.append_child(
    head,
    HTML.parse(
      '<meta name="twitter:title" content="'  .. HTML.strip_tags(title) .. '" />'
    )
  )
end

HTML.append_child(
  head,
  HTML.parse(
    '<meta property="og:url" content ="' .. base_url .. page_url .. '" />'
  )
)
HTML.append_child(
  head,
  HTML.parse(
    '<meta property="twitter:url" content ="' .. base_url .. page_url .. '" />'
  )
)

description = HTML.select_one(page, "#meta-tags .description")
if description then
  description_contents = HTML.strip_tags(description)
  description_contents = Regex.replace_all(description_contents, "\n", " ")

  HTML.append_child(
    head,
    HTML.parse(
      '<meta name="description" content="'
      .. description_contents .. '">'
    )
  )
  HTML.append_child(
    head,
    HTML.parse(
      '<meta property="og:description" content="'
      .. description_contents .. '">'
    )
  )
  HTML.append_child(
    head,
    HTML.parse(
      '<meta name="twitter:description" content="'
      .. description_contents .. '">'
    )
  )
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
