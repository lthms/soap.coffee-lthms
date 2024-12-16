let read_exn path = Option.get (Website_content.read path)
let assert_f ~error_msg f v = if not (f v) then failwith error_msg else v
let gzip_encoded = ("Content-Encoding", "gzip")

(** [gzip content] returns [content] compressed with the GZIP algorithm (level 6). *)
let gzip content =
  let inc, ouc = Unix.pipe () in
  let ouc = Gzip.open_out_chan ~level:6 Unix.(out_channel_of_descr ouc) in
  let _writer =
    Domain.spawn (fun () ->
        Gzip.output_substring ouc content 0 String.(length content);
        Gzip.close_out ouc)
  in
  let res = In_channel.input_all Unix.(in_channel_of_descr inc) in
  Unix.close inc;
  res

let content_types =
  [
    (".html", "text/html");
    (".css", "text/css");
    (".xml", "text/xml");
    (".png", "image/png");
    (".svg", "image/svg+xml");
    (".gz", "application/gzip");
    (".pub", "text/plain");
  ]

let one_year = 3600 * 24 * 365
let five_minutes = 60 * 5
let cache_policy duration = Format.sprintf "public, max-age=%d" duration

let cache_configuration =
  [ (".png", cache_policy one_year); (".svg", cache_policy one_year) ]

let content_type_header path =
  List.filter_map
    (fun (ext, content_type) ->
      if String.ends_with ~suffix:ext path then
        Some ("Content-Type", content_type)
      else None)
    content_types
  |> assert_f
       ~error_msg:Format.(sprintf "Unsupported file type %s" path)
       (( <> ) [])

let cache_header path =
  match
    List.filter_map
      (fun (ext, content_type) ->
        if String.ends_with ~suffix:ext path then
          Some ("Cache-Control", content_type)
        else None)
      cache_configuration
  with
  | [] -> [ ("Cache-Control", cache_policy five_minutes) ]
  | result -> result

let to_directive str =
  match String.split_on_char ';' str |> List.map String.trim with
  | [ x ] -> Some x
  | [ x; y ] -> (
      match String.split_on_char '=' y |> List.map String.trim with
      | [ "q"; "0" ] -> None
      | [ "q"; _ ] -> Some x
      | _ -> None)
  | _ -> None

let contains ~value header =
  String.split_on_char ',' header
  |> List.to_seq |> Seq.map String.trim
  |> Seq.filter_map to_directive
  |> Seq.exists (( = ) value)

let make_handler ~headers ~etag ~gzip_content ~content path =
  let etag_gzip = Format.sprintf "\"%s+gzip\"" etag in
  let etag = Format.sprintf "\"%s\"" etag in
  let gzip_headers = gzip_encoded :: ("ETag", etag_gzip) :: headers in
  let identity_headers = ("ETag", etag) :: headers in
  Dream.get path (fun req ->
      match Dream.headers req "If-None-Match" with
      | [ previous_etag ] when previous_etag = etag || previous_etag = etag_gzip
        ->
          Lwt.return
          @@ Dream.response
               ~headers:(("ETag", previous_etag) :: headers)
               ~code:304 ""
      | _ -> (
          match Dream.headers req "Accept-Encoding" with
          | accepted_encodings
            when List.exists (contains ~value:"gzip") accepted_encodings ->
              Lwt.return @@ Dream.response ~headers:gzip_headers gzip_content
          | _ -> Lwt.return @@ Dream.response ~headers:identity_headers content))

let make_handler_remove_suffix ~headers ~etag ~gzip_content ~content path suffix
    =
  if String.ends_with ~suffix path then
    let alt_path =
      String.sub path 0 (String.length path - String.length suffix)
    in
    [ make_handler ~headers ~etag ~gzip_content ~content alt_path ]
  else []

let wrap_with_log before after k =
  Dream.log "%s" before;
  let res = k () in
  Dream.log "%s" after;
  res

let website_handlers =
  wrap_with_log "Computing handlers..." "Handlers are ready" @@ fun () ->
  Dream.scope "~lthms" []
  @@ List.concat_map
       (fun path ->
         let content = read_exn path in
         let gzip_content = gzip content in
         let etag = Sha256.(string content |> to_hex) in
         let headers = content_type_header path @ cache_header path in
         if path = "index.html" then
           (* Special case to deal with "index.html" which needs to be
              recognized by the route "/" *)
           [
             make_handler ~headers ~etag ~content ~gzip_content "/";
             make_handler ~headers ~etag ~content ~gzip_content "";
             make_handler ~headers ~etag ~content ~gzip_content "index.html";
           ]
         else
           make_handler_remove_suffix ~headers ~etag ~content ~gzip_content path
             "/index.html"
           @ make_handler_remove_suffix ~headers ~etag ~content ~gzip_content
               path "index.html"
           @ [ make_handler ~headers ~etag ~content ~gzip_content path ])
       Website_content.file_list

let () =
  Dream.run ~port:8901 @@ Dream.logger @@ Dream.router [ website_handlers ]
