  $c ( $.  
  $c ) $.  
  $c -> $. 
  $c -. $. 
  $c wff $. 
  $c |- $.
    $v ph $.  
  $v ps $.  
  $v ch $.  
  $v th $.  
  $v ta $.  
  $v et $.  
  $v ze $.  
  $v si $.  
  $v rh $.  
  $v mu $.  
  $v la $.  
  $v ka $.
  wph $f wff ph $.
  
  wps $f wff ps $.
  
  wch $f wff ch $.
  
  wth $f wff th $.
  
  wta $f wff ta $.
  
  wet $f wff et $.
  
  wze $f wff ze $.
  
  wsi $f wff si $.
  
  wrh $f wff rh $.
  
  wmu $f wff mu $.
  
  wla $f wff la $.
  
  wka $f wff ka $.
  
  wn $a wff -. ph $.
  
  wi $a wff ( ph -> ps ) $.
  ${
    
    min $e |- ph $.
    
    maj $e |- ( ph -> ps ) $.
    
    ax-mp $a |- ps $.
  $}
  
  ax-1 $a |- ( ph -> ( ps -> ph ) ) $.
  
  ax-2 $a |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) ) $.
  
  ax-3 $a |- ( ( -. ph -> -. ps ) -> ( ps -> ph ) ) $.
  ${
    mp2.0 $e |- ph $.
    mp2.2 $e |- ps $.
    mp2.3 $e |- ( ph -> ( ps -> ch ) ) $.
    $( A double modus ponens inference. $)
    mp2 $p |- ch $=
      wps wch mp2.2 wph wps wch wi mp2.0 mp2.3 ax-mp ax-mp $.
  $}
  ${
    a1i.1 $e |- ph $.
    
    a1i $p |- ( ps -> ph ) $=
      ( wi ax-1 ax-mp ) ABADCABEF $.
  $}
  ${
    a2i.1 $e |- ( ph -> ( ps -> ch ) ) $.
    
    a2i $p |- ( ( ph -> ps ) -> ( ph -> ch ) ) $=
      ( wi ax-2 ax-mp ) ABCEEABEACEEDABCFG $.
  $}
  ${
    mpd.1 $e |- ( ph -> ps ) $.
    mpd.2 $e |- ( ph -> ( ps -> ch ) ) $.
    
    mpd $p |- ( ph -> ch ) $=
      ( wi a2i ax-mp ) ABFACFDABCEGH $.
  $}
  ${
    
    syl.1 $e |- ( ph -> ps ) $.
    
    syl.2 $e |- ( ps -> ch ) $.
    
    syl $p |- ( ph -> ch ) $=
      ( wi a1i mpd ) ABCDBCFAEGH $.
  $}
  
  $( Principle of
     identity. $)
  id $p |- ( ph -> ph ) $=
    ( wi ax-1 mpd ) AAABZAAACAECD $.
  
  idd $p |- ( ph -> ( ps -> ps ) ) $=
    ( wi id a1i ) BBCABDE $.
  ${
    a1d.1 $e |- ( ph -> ps ) $.
    
    a1d $p |- ( ph -> ( ch -> ps ) ) $=
      ( wi ax-1 syl ) ABCBEDBCFG $.
  $}
  ${
    sylcom.1 $e |- ( ph -> ( ps -> ch ) ) $.
    sylcom.2 $e |- ( ps -> ( ch -> th ) ) $.
    
    sylcom $p |- ( ph -> ( ps -> th ) ) $=
      ( wi a2i syl ) ABCGBDGEBCDFHI $.
  $}
  ${
    syl5com.1 $e |- ( ph -> ps ) $.
    syl5com.2 $e |- ( ch -> ( ps -> th ) ) $.
    
    syl5com $p |- ( ph -> ( ch -> th ) ) $=
      ( a1d sylcom ) ACBDABCEGFH $.
  $}
  ${
    com12.1 $e |- ( ph -> ( ps -> ch ) ) $.
    
    com12 $p |- ( ps -> ( ph -> ch ) ) $=
      ( id syl5com ) BBACBEDF $.
  $}
  ${
    syl5.1 $e |- ( ph -> ps ) $.
    syl5.2 $e |- ( ch -> ( ps -> th ) ) $.
    
    syl5 $p |- ( ch -> ( ph -> th ) ) $=
      ( syl5com com12 ) ACDABCDEFGH $.
  $}
  ${
    syl6.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syl6.2 $e |- ( ch -> th ) $.
    
    syl6 $p |- ( ph -> ( ps -> th ) ) $=
      ( wi a1i sylcom ) ABCDECDGBFHI $.
  $}
  
  pm2.27 $p |- ( ph -> ( ( ph -> ps ) -> ps ) ) $=
    ( wi id com12 ) ABCZABFDE $.
  ${
    pm2.43i.1 $e |- ( ph -> ( ph -> ps ) ) $.
    
    pm2.43i $p |- ( ph -> ps ) $=
      ( id mpd ) AABADCE $.
  $}
  
  con4 $p |- ( ( -. ph -> -. ps ) -> ( ps -> ph ) ) $=
    ( ax-3 ) ABC $.
  ${
    con4d.1 $e |- ( ph -> ( -. ps -> -. ch ) ) $.
    
    con4d $p |- ( ph -> ( ch -> ps ) ) $=
      ( wn wi con4 syl ) ABECEFCBFDBCGH $.
  $}
  ${
    pm2.21d.1 $e |- ( ph -> -. ps ) $.
    
    pm2.21d $p |- ( ph -> ( ps -> ch ) ) $=
      ( wn a1d con4d ) ACBABECEDFG $.
  $}
  
  pm2.21 $p |- ( -. ph -> ( ph -> ps ) ) $=
    ( wn id pm2.21d ) ACZABFDE $.
  
  pm2.18 $p |- ( ( -. ph -> ph ) -> ph ) $=
    ( wn wi pm2.21 a2i con4d pm2.43i ) ABZACZAIAIHAIBZAJDEFG $.
  ${
    pm2.18d.1 $e |- ( ph -> ( -. ps -> ps ) ) $.
    
    pm2.18d $p |- ( ph -> ps ) $=
      ( wn wi pm2.18 syl ) ABDBEBCBFG $.
  $}
  
  $( For test discouraged (New usage is discouraged.) $)
  notnotr $p |- ( -. -. ph -> ph ) $=
    ( wn pm2.21 pm2.18d ) ABZBAEACD $.
  ${
    con2d.1 $e |- ( ph -> ( ps -> -. ch ) ) $.
    
    con2d $p |- ( ph -> ( ch -> -. ps ) ) $=
      ( wn notnotr syl5 con4d ) ABEZCIEBACEBFDGH $.
  $}
  ${
    mt2d.1 $e |- ( ph -> ch ) $.
    mt2d.2 $e |- ( ph -> ( ps -> -. ch ) ) $.
    
    mt2d $p |- ( ph -> -. ps ) $=
      ( wn con2d mpd ) ACBFDABCEGH $.
  $}
  ${
    nsyl3.1 $e |- ( ph -> -. ps ) $.
    nsyl3.2 $e |- ( ch -> ps ) $.
    
    nsyl3 $p |- ( ch -> -. ph ) $=
      ( wn wi a1i mt2d ) CABEABFGCDHI $.
  $}
  ${
    con2i.a $e |- ( ph -> -. ps ) $.
    
    con2i $p |- ( ps -> -. ph ) $=
      ( id nsyl3 ) ABBCBDE $.
  $}
  
  notnot $p |- ( ph -> -. -. ph ) $=
    ( wn id con2i ) ABZAECD $.
  ${
    con1d.1 $e |- ( ph -> ( -. ps -> ch ) ) $.
    
    con1d $p |- ( ph -> ( -. ch -> ps ) ) $=
      ( wn notnot syl6 con4d ) ABCEZABECIEDCFGH $.
  $}
  ${
    mt3d.1 $e |- ( ph -> -. ch ) $.
    mt3d.2 $e |- ( ph -> ( -. ps -> ch ) ) $.
    
    mt3d $p |- ( ph -> ps ) $=
      ( wn con1d mpd ) ACFBDABCEGH $.
  $}
  ${
    nsyl2.1 $e |- ( ph -> -. ps ) $.
    nsyl2.2 $e |- ( -. ch -> ps ) $.
    
    nsyl2 $p |- ( ph -> ch ) $=
      ( wn wi a1i mt3d ) ACBDCFBGAEHI $.
  $}
  ${
    con1i.1 $e |- ( -. ph -> ps ) $.
    
    con1i $p |- ( -. ps -> ph ) $=
      ( wn id nsyl2 ) BDZBAGECF $.
  $}
  ${
    con3d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    
    con3d $p |- ( ph -> ( -. ch -> -. ps ) ) $=
      ( wn notnotr syl5 con1d ) ABEZCIEBACBFDGH $.
  $}
  ${
    con3rr3.1 $e |- ( ph -> ( ps -> ch ) ) $.
    
    con3rr3 $p |- ( -. ch -> ( ph -> -. ps ) ) $=
      ( wn con3d com12 ) ACEBEABCDFG $.
  $}
  
  pm3.2im $p |- ( ph -> ( ps -> -. ( ph -> -. ps ) ) ) $=
    ( wn wi pm2.27 con2d ) AABCZDBAGEF $.
  ${
    impi.1 $e |- ( ph -> ( ps -> ch ) ) $.
    
    impi $p |- ( -. ( ph -> -. ps ) -> ch ) $=
      ( wn wi con3rr3 con1i ) CABEFABCDGH $.
  $}
  ${
    expi.1 $e |- ( -. ( ph -> -. ps ) -> ch ) $.
    
    expi $p |- ( ph -> ( ps -> ch ) ) $=
      ( wn wi pm3.2im syl6 ) ABABEFECABGDH $.
  $}
  
  simprim $p |- ( -. ( ph -> -. ps ) -> ps ) $=
    ( idd impi ) ABBABCD $.
  
  $c <-> $.
  
  wb $a wff ( ph <-> ps ) $.
  
  df-bi $a |- -. ( ( ( ph <-> ps ) -> -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) )
        -> -. ( -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) -> ( ph <-> ps ) ) ) $.
  
  impbi $p |- ( ( ph -> ps ) -> ( ( ps -> ph ) -> ( ph <-> ps ) ) ) $=
    ( wi wb wn df-bi simprim ax-mp expi ) ABCZBACZABDZLJKECEZCZMLCZECEOABFNOGHI
    $.
  ${
    impbii.1 $e |- ( ph -> ps ) $.
    impbii.2 $e |- ( ps -> ph ) $.
    
    impbii $p |- ( ph <-> ps ) $=
      ( wi wb impbi mp2 ) ABEBAEABFCDABGH $.
  $}
  

