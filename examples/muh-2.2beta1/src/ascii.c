/* $Id: ascii.c,v 1.2 2009-02-17 08:55:21 chinwn Exp $
 * -------------------------------------------------------
 * Copyright (c) 1998-2002 Sebastian Kienzl <zap@riot.org>
 * -------------------------------------------------------
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 */

/* bernhard weitzhofer <nyl@riot.org> did these asciis. thanks a lot! */

#include "ascii.h"

char pics[ 3 ][ PIC_Y ][ PIC_X ] =
{
{ "                  \\_/ ",
  " muh! ( _ )      -(_)-",
  "   \\  ~O o~__     / \\ ",
  "      (._.) |\\        ",
  "________|_|_|_________" },

{ " *     *           _  ",
  "    *       *   * (_) ",
  "      ( _ )   *       ",
  " *    ~u u~__     *   ",
  "______(._.)_|\\_______" },

{ "                  /\\  ",
  "x-muh!( _ )      / o\\ ",
  "    \\ ~@ *~__   /o   \\",
  "      (._.) |\\  /___o\\",
  "________|_|_|_____||__" } };
