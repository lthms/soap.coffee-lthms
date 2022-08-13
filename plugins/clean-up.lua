function remove_if_empty(html)
   if String.trim(HTML.inner_html(html)) == "" then
      HTML.delete(html)
   end
end

function remove_all_if_empty(cls)
   local elements = HTML.select(page, cls)

   local i = 1
   while elements[i] do
      local element = elements[i]
      remove_if_empty(element)
      i = i + 1
   end
end

remove_all_if_empty("p") -- introduced by org-mode
remove_all_if_empty("div.code") -- introduced by coqdoc
