import cv2
import numpy as np


class ReferenceMarker:
    def getPlaneAndMask(self, plane, coordinates):
        h, w, _ = plane.shape
        mask = np.zeros((h, w), dtype="uint8")
        cv2.rectangle(mask, (coordinates[2], coordinates[0]),
                      (coordinates[3], coordinates[1]), 255, -1)
        plane = cv2.bitwise_and(plane, plane, mask=mask)
        return plane[coordinates[0]:coordinates[1], coordinates[2]:coordinates[3]], mask
