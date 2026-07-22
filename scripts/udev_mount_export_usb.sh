#!/usr/bin/env bash
set -euo pipefail

DEVPATH="${1:-}"
MOUNT_POINT="/media/usb_export"

if [[ -z "${DEVPATH}" ]]; then
  echo "usage: $0 /dev/sdXN" >&2
  exit 2
fi

if ! [[ -b "${DEVPATH}" ]]; then
  echo "not a block device: ${DEVPATH}" >&2
  exit 4
fi

INTERNAL_SRC="$(findmnt -n -o SOURCE /media/usb_internal 2>/dev/null || true)"
INTERNAL_PKNAME=""
if [[ -n "${INTERNAL_SRC}" && -b "${INTERNAL_SRC}" ]]; then
  INTERNAL_PKNAME="$(lsblk -n -o PKNAME "${INTERNAL_SRC}" 2>/dev/null | sed -n '1p' || true)"
  if [[ -z "${INTERNAL_PKNAME}" ]]; then
    INTERNAL_PKNAME="$(basename "${INTERNAL_SRC}")"
  fi
fi

DEV_PKNAME="$(lsblk -n -o PKNAME "${DEVPATH}" 2>/dev/null | sed -n '1p' || true)"
if [[ -z "${DEV_PKNAME}" ]]; then
  DEV_PKNAME="$(basename "${DEVPATH}")"
fi

if [[ -n "${INTERNAL_SRC}" && "${DEVPATH}" == "${INTERNAL_SRC}" ]]; then
  echo "refusing internal device ${DEVPATH}" >&2
  exit 3
fi
if [[ -n "${INTERNAL_PKNAME}" && "${DEV_PKNAME}" == "${INTERNAL_PKNAME}" ]]; then
  echo "refusing device ${DEVPATH} on internal disk ${INTERNAL_PKNAME}" >&2
  exit 3
fi

mkdir -p "${MOUNT_POINT}"

# If mountpoint is already mounted:
# - keep it if same source
# - otherwise unmount so requested device can be mounted
if findmnt -n "${MOUNT_POINT}" >/dev/null 2>&1; then
  CURRENT_SRC="$(findmnt -n -o SOURCE "${MOUNT_POINT}" || true)"
  if [[ "${CURRENT_SRC}" == "${DEVPATH}" ]]; then
    exit 0
  fi
  umount "${MOUNT_POINT}" || true
fi

# If device already mounted somewhere, bind it to expected mountpoint.
CURRENT_MNT="$(lsblk -n -o MOUNTPOINT "${DEVPATH}" | sed -n '1p' || true)"
if [[ -n "${CURRENT_MNT}" && "${CURRENT_MNT}" != "${MOUNT_POINT}" ]]; then
  mount --bind "${CURRENT_MNT}" "${MOUNT_POINT}"
  exit 0
fi

mount -o rw,uid=1000,gid=1000,umask=0022 "${DEVPATH}" "${MOUNT_POINT}"
sync
