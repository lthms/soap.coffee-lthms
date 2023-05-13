function get_title_from_path (path)
   if Sys.is_file(path) then
      local content_raw = Sys.read_file(path)
      local content_dom = HTML.parse(content_raw)
      local title = HTML.select_one(content_dom, "h1")

      if title then
         return String.trim(HTML.inner_html(title))
      else
         Plugin.fail(path .. ' has no <h1> tag')
      end
   else
      Log.warning('Missing file: ' .. path)
   end
end

function generate_nav_item_from_title (title, url, template)
    local env = {}
    env["url"] = url
    env["title"] = title
    local new_content = String.render_template(template, env)
    return HTML.parse(new_content)
end

function generate_nav_items (cwd, cls, template)
  local elements = HTML.select(page, cls)

  local i = 1
  while elements[i] do
    local element = elements[i]
    local url = HTML.strip_tags(element)
    local path = Sys.join_path(cwd, url)
    local title_str = get_title_from_path(path)

    HTML.replace_content(
      element,
      generate_nav_item_from_title(title_str, url, template)
    )

    i = i + 1
  end
end

cwd = build_dir

home_template = 'This page is part of the series “<a href="/{{ url }}">{{ title }}</a>.”'
nav_template = '<a href="/{{ url }}">{{ title }}</a>'

generate_nav_items(cwd, ".series", home_template)
generate_nav_items(cwd, ".series-prev", nav_template)
generate_nav_items(cwd, ".series-next", nav_template)
