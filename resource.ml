
let strinng_title = ref ("Sleek": string)

let string_menu_bar = ref ("<menubar name='MenuBar'>\
      <menu action='FileMenu'>\
        <menuitem action='New'/>\
        <menuitem action='Open'/>\
        <menuitem action='Save'/>\
        <separator/>\
        <menuitem action='Quit'/>\
      </menu>\n
      <menu action='OptionsMenu'>\
        <menu action='ProversMenu'>\
          <menuitem action='Omega'/>\
          <menuitem action='Mona'/>\
          <menuitem action='Redlog'/>\
        </menu>\
        <menuitem action='EPS'/>\
        <menuitem action='EAP'/>\
      </menu>\
      <menu action='HelpMenu'>\
        <menuitem action='About'/>\
      </menu>\
    </menubar>": string)

let string_tool_bar = ref ("<toolbar name='ToolBar'>\
      <toolitem action='New'/>\
      <toolitem action='Open'/>\
      <toolitem action='Save'/>\
      <separator/>\
      <toolitem action='Execute'/>\
    </toolbar>":string)
