/* Menu button in the site header (home page and the four trade pages), for phones and tablets where the links are folded away.
   The menu is a <details> and works without this file; this only closes it after a tap on one of its links (an in-page link would
   otherwise leave it covering the page), after a tap anywhere outside it, and on Escape. */
(function () {
  var menu = document.querySelector('details.navmenu');
  if (!menu) return;
  function close(giveFocusBack) {
    if (!menu.open) return;
    menu.open = false;
    if (giveFocusBack) {
      var button = menu.querySelector('summary');
      if (button) button.focus();
    }
  }
  menu.addEventListener('click', function (e) {
    if (e.target && e.target.closest && e.target.closest('a')) close(false);
  });
  document.addEventListener('click', function (e) {
    if (menu.open && !menu.contains(e.target)) close(false);
  });
  document.addEventListener('keydown', function (e) {
    if (e.key === 'Escape') close(true);
  });
})();
