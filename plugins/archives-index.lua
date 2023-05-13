env = {}

container = HTML.select_one(page, config["index_selector"])
container_content = HTML.inner_html(container)

if Value.is_string(container_content) then
  container_content = String.to_number(container_content)
end

template = nil
pages = {}

if container_content then
  env['contents'] = Table.take(site_index, container_content)
  template = "index_short_template_file"
else
  env['contents'] = site_index

  template = Sys.read_file(config['index_rss_template_file'])

  path = Sys.join_path(target_dir, 'index.xml')
  Sys.write_file(path, String.render_template(template, env))

  template = "index_full_template_file"
end

template = Sys.read_file(config[template])
rendered_entries = HTML.parse(String.render_template(template, env))
HTML.replace_content(container, rendered_entries)
