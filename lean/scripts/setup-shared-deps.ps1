<#
.SYNOPSIS
  Point this project's `.lake/packages` at a shared, toolchain-keyed dependency store.

.DESCRIPTION
  A Lake project keeps its dependencies in `.lake/packages`. For a Mathlib-dependent
  project that is a source checkout plus build artifacts totalling several gigabytes, and
  every project on the machine pays it again.

  This script replaces `.lake/packages` with a Windows directory junction into

      $HOME\.lean-shared\packages\<toolchain>

  so that every project pinned to the same toolchain shares one copy. Only `packages` is
  redirected: `.lake/build` stays project-local, so projects never clobber each other's
  own build output.

  The store is keyed by toolchain because the Mathlib revision a project can use is
  determined by its `lean-toolchain`. Two projects on different toolchains get different
  stores and do not fight over the checkout.

  Idempotent: safe to re-run. Requires no administrator rights (junctions, unlike
  symlinks, do not need elevation).

.PARAMETER StoreRoot
  Root of the shared store. Defaults to `$HOME\.lean-shared\packages`.

.PARAMETER Force
  Replace an existing real `.lake/packages` directory. Its contents are deleted, not
  merged. Lake re-fetches into the shared store on the next build.
#>
[CmdletBinding()]
param(
  [string]$StoreRoot = (Join-Path $HOME '.lean-shared\packages'),
  [switch]$Force
)

$ErrorActionPreference = 'Stop'

$repo = Split-Path -Parent $PSScriptRoot
$toolchainFile = Join-Path $repo 'lean-toolchain'
if (-not (Test-Path $toolchainFile)) {
  throw "No lean-toolchain at $toolchainFile - is $repo a Lake project?"
}

# "leanprover/lean4:v4.28.0" -> "v4.28.0"
$toolchain = (Get-Content $toolchainFile -Raw).Trim()
$key = ($toolchain -split ':')[-1]
if ([string]::IsNullOrWhiteSpace($key)) { throw "Could not read a toolchain version from '$toolchain'." }

$store = Join-Path $StoreRoot $key
$link = Join-Path $repo '.lake\packages'

New-Item -ItemType Directory -Force -Path $store | Out-Null
New-Item -ItemType Directory -Force -Path (Join-Path $repo '.lake') | Out-Null

$existing = Get-Item $link -ErrorAction SilentlyContinue
if ($null -ne $existing) {
  if ($existing.LinkType -eq 'Junction' -or $existing.LinkType -eq 'SymbolicLink') {
    $current = @($existing.Target)[0]
    if ($current -eq $store) {
      Write-Host "Already linked: .lake\packages -> $store"
      exit 0
    }
    Write-Host "Relinking .lake\packages: $current -> $store"
    (Get-Item $link).Delete()
  }
  elseif ($Force) {
    Write-Host "Removing existing .lake\packages (-Force)"
    Remove-Item -Recurse -Force $link
  }
  else {
    throw ".lake\packages already exists as a real directory. Re-run with -Force to " +
          "discard it (Lake will re-fetch into $store), or move it there by hand."
  }
}

New-Item -ItemType Junction -Path $link -Target $store | Out-Null
Write-Host "Linked .lake\packages -> $store"
Write-Host ""
Write-Host "Next: lake build" -ForegroundColor Cyan
